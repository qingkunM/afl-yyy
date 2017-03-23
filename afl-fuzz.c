/*
 american fuzzy lop - fuzzer code
 --------------------------------

 Written and maintained by Michal Zalewski <lcamtuf@google.com>

 Forkserver design by Jann Horn <jannhorn@googlemail.com>

 Copyright 2013, 2014, 2015 Google Inc. All rights reserved.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at:

 http://www.apache.org/licenses/LICENSE-2.0

 This is the real deal: the program takes an instrumented binary and
 attempts a variety of basic fuzzing tricks, paying close attention to
 how they affect the execution path.

 */

#define AFL_MAIN
#define MESSAGES_TO_STDOUT

#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64

#include "config.h"
#include "types.h"
#include "debug.h"
#include "alloc-inl.h"
#include "hash.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <signal.h>
#include <dirent.h>
#include <ctype.h>
#include <fcntl.h>
#include <termios.h>
#include <dlfcn.h>
#include <netdb.h>

#include <sys/wait.h>
#include <sys/time.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <sys/sendfile.h>

#ifdef XIAOSA

	#include <sys/ipc.h>

#endif

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)
#  include <sys/sysctl.h>
#endif /* __APPLE__ || __FreeBSD__ || __OpenBSD__ */

/* Lots of globals, but mostly for the status UI and other things where it
 really makes no sense to haul them around as function parameters. */

static u8 *in_dir , /* Input directory with test cases  */
*out_file , /* File to fuzz, if any             */
*out_dir , /* Working & output directory       */
*sync_dir , /* Synchronization directory        */
*sync_id , /* Fuzzer ID                        */
*use_banner , /* Display banner                   */
*in_bitmap , /* Input bitmap                     */
*doc_path , /* Path to documentation dir        */
*target_path , /* Path to target binary            */
*orig_cmdline; /* Original command line            */

static u32 exec_tmout = EXEC_TIMEOUT; /* Configurable exec timeout (ms)   */
static u64 mem_limit = MEM_LIMIT; /* Memory cap for child (MB)        */

static u32 stats_update_freq = 1; /* Stats update frequency (execs)   */

static u8 	skip_deterministic , /* Skip deterministic stages?       */
			force_deterministic , /* Force deterministic stages?      */
			use_splicing , /* Recombine input files?           */
			dumb_mode , /* Run in non-instrumented mode?    */
			score_changed , /* Scoring for favorites changed?   */
			kill_signal , /* Signal that killed the child     */
			resuming_fuzz , /* Resuming an older fuzzing job?   */
			timeout_given , /* Specific timeout given?          */
			not_on_tty , /* stdout is not a tty              */
			term_too_small , /* terminal dimensions too small    */
			uses_asan , /* Target uses ASAN?                */
			no_forkserver , /* Disable forkserver?              */
			crash_mode , /* Crash mode! Yeah!                */
			in_place_resume , /* Attempt in-place resume?         */
			auto_changed , /* Auto-generated tokens changed?   */
			no_cpu_meter_red , /* Feng shui on the status screen   */
			no_var_check , /* Don't detect variable behavior   */  //随机路径 默认0,要测试
			bitmap_changed = 1 , /* Time to update bitmap?           */
			qemu_mode , /* Running in QEMU mode?            */
			skip_requested , /* Skip request, via SIGUSR1        */
			run_over10m; /* Run time over 10 minutes?        */

static s32 	out_fd , /* Persistent fd for out_file       */
			dev_urandom_fd = -1 , /* Persistent fd for /dev/urandom   */  //随机数文件
			dev_null_fd = -1 , /* Persistent fd for /dev/null      */
			fsrv_ctl_fd , /* Fork server control pipe (write) */
			fsrv_st_fd; /* Fork server status pipe (read)   */

static s32 forksrv_pid , /* PID of the fork server           */
			child_pid = -1 , /* PID of the fuzzed program        */
			out_dir_fd = -1; /* FD of the lock file              */

static 	u8* trace_bits; /* SHM with instrumentation bitmap  */ //包含滚筒值 单次测试用例
#ifdef XIAOSA
static	u32* virgin_counts;    /*SHM to save the execution number of the each tuple*/
#endif

static 	u8 	virgin_bits [ MAP_SIZE ] , /* Regions yet untouched by fuzzing */ //包含滚筒值
			virgin_hang [ MAP_SIZE ] , /* Bits we haven't seen in hangs    */
			virgin_crash [ MAP_SIZE ]; /* Bits we haven't seen in crashes  */

static 	s32	shm_id; /* ID of the SHM region             */

#ifdef XIAOSA
static	s32	shm_id_virgin_counts;    /* id of SHM, to save the execution number of the each tuple*/
#endif

static volatile u8 stop_soon , /* Ctrl-C pressed?                  */
clear_screen = 1 , /* Window resized?                  */
child_timed_out; /* Traced process timed out?        */  //判断子进程是否超时,1为超时

static u32 	queued_paths ,			/* Total number of queued testcases */ //queue下的数量,包含初始测试用例, 比id大1.
			queued_variable , 		/* Testcases with variable behavior */
			queued_at_start , 		/* Total number of initial inputs   */  //初始的数量
			queued_discovered ,		/* Items discovered during this run */ //本次fuzz增加的测试用例数量,不包含初始
			queued_imported , 		/* Items imported via -S            */  //导入的数量
			queued_favored , 		/* Paths deemed favorable           */ //cull_queue之后的测试用例数量
			queued_with_cov , 		/* Paths with new coverage bytes    */ //发现一个新的元组关系就+1(不考虑滚筒)
			pending_not_fuzzed ,	/* Queued but not done yet          */ //还没有fuzz过的测试用例
			pending_favored , 		/* Pending favored paths            */ //待fuzzone的测试用例,第二轮之后不判断,cull优化后的数量
			cur_skipped_paths , 	/* Abandoned inputs in cur cycle    */ //表示每一轮中放弃的测试用例数量
			cur_depth , 			/* Current path depth               */  //测试深度
			max_depth , 			/* Max path depth                   */
			useless_at_start , 		/* Number of useless starting path  */
			current_entry , 		/* Current queue entry ID           */
			havoc_div = 1; 			/* Cycle count divisor for havoc    */

#ifdef XIAOSA

	static u32 	last_big_cycle_case_num, /*the number of the testcase in the queue catalog befor the last big cycle*/
			add_case_num_last_big_cycle, /*the add number of the testcase in the queue catalog during the last big cycle*/

			last_big_cycle_crash_num, /*the number of the testcase in the crash catalog befor the last big cycle*/
			add_crash_num_last_big_cycle; /*the add number of the testcase in the crash catalog during the last big cycle*/
#endif

static u64 	total_crashes , 	/* Total number of crashes          */
			unique_crashes , 	/* Crashes with unique signatures   */
			total_hangs , 		/* Total number of hangs            */
			unique_hangs , 		/* Hangs with unique signatures     */
			total_execs , 		/* Total execve() calls             */
			start_time , 		/* Unix start time (ms)             */
			last_path_time , 	/* Time for most recent path (ms)   */
			last_crash_time , 	/* Time for most recent crash (ms)  */
			last_hang_time , 	/* Time for most recent hang (ms)   */
			queue_cycle , 		/* Queue round counter              */
			cycles_wo_finds , 	/* Cycles without any new paths     */
			trim_execs , 		/* Execs done to trim input files   */  //trim的次数
			bytes_trim_in , 	/* Bytes coming into the trimmer    */  //进入trim的字节数
			bytes_trim_out , 	/* Bytes coming outa the trimmer    */ //被trim后剩余的字节数累计
			blocks_eff_total , 	/* Blocks subject to effector maps  */ //总共的block数量
			blocks_eff_select; 	/* Blocks selected as fuzzable      */ //关键block的数量

#ifdef XIAOSA
		u64	big_cycle_start_time;  /*the start time of every big cycle*/ //in second level
		u64	big_cycle_stop_time;   /*the stop time of every big cycle*/
		u64 time_of_big_cycle;	/*the  time of every big cycle*/
		u64 main_start_time;	 /*record the start time of fucntion main, in us*/
#endif

static u32 subseq_hangs; /* Number of hangs in a row         */

static u8 *stage_name = "init" , /* Name of the current fuzz stage   */
*stage_short , /* Short stage name                 */
*syncing_party; /* Currently syncing with...        */  //表示同步的fuzzer名称

static s32 stage_cur , stage_max; /* Stage progression                */ //记录了某一阶段的测试次数
static s32 splicing_with = -1; /* Splicing with which test case?   */ //随机选择一个别的测试用例

static u32 syncing_case; /* Syncing with case #...           */

static s32 stage_cur_byte , /* Byte offset of current stage op  */ //havod阶段会设置成-1
		stage_cur_val; /* Value used for stage op          */  //表示加减的值

static u8 stage_val_type; /* Value type (STAGE_VAL_*)         */

static u64 stage_finds [ 32 ] , /* Patterns found per fuzz stage    */
stage_cycles [ 32 ]; /* Execs per fuzz stage             */

static u32 rand_cnt; /* Random number counter            */

static u64 total_cal_us , /* Total calibration time (us)      */
total_cal_cycles; /* Total calibration cycles         */

static u64 total_bitmap_size , /* Total bit count for all bitmaps  */  //元组关系的数量
		total_bitmap_entries; /* Number of bitmaps counted        */  //被测试的数量

static u32 cpu_core_count; /* CPU core count                   */

static FILE* plot_file; /* Gnuplot output file              */

/* Globals for network support */

static struct addrinfo *N_results = NULL , /* for results from getaddrinfo() */
*N_rp = NULL; /* to iterate through N_results[] */

static struct sockaddr_storage N_myaddr; /* to hold send port info        */
static struct sockaddr_storage N_server_addr; /* and server (send side)   */
static socklen_t N_myaddrlen = sizeof(struct sockaddr_storage);
/* and length of both               */

static u32 N_option_specified = 0; /* 1 if a -N option is present      */
static u8* N_option_string = 0; /* points to copy of -N option str  */
static u32 N_slen = 0; /* length of the -N option string   */
static u32 N_valid = 0; /* 1 if valid URL option to -N      */
static u32 N_fuzz_client = 0; /* 1 if target is a network client  */
static u32 N_myaddr_valid = 0; /* use established conn or addr     */
static s32 N_fd; /* for network file descriptor      */

static u32 N_timeout_given = 0; /* use delay before network I/O     */
static u32 N_exec_tmout = 0; /* network I/O delay in msec        */
static struct timespec N_it; /* structure for nanosleep() call   */

struct queue_entry
{

	u8* fname; /* File name for the test case      */
	u32 len; /* Input length                     */

	u8 	cal_failed , /* Calibration failed?              */
		trim_done , /* Trimmed?                         */
		was_fuzzed , /* Had any fuzzing done yet?        */
		passed_det , /* Deterministic stages passed?     */
		has_new_cov , /* Triggers new coverage?           */ //表示该测试用例变异后生成新的元组关系
		var_behavior , /* Variable behavior?               */
		favored , /* Currently favored?               */ //判断当前测试用例的受欢迎程度
		fs_redundant; /* Marked as redundant in the fs?   */

	u32 bitmap_size , /* Number of bits set in bitmap     */ //表示有多少元组跳跃关系
		exec_cksum; /* Checksum of the execution trace  */

	u64 exec_us , /* Execution time (us)              */  //每一个测试的平均时间
		handicap , /* Number of queue cycles behind    */
		depth; /* Path depth                       */  //这个怎么定义的?

	u8* trace_mini; /* Trace bytes, if kept  每一位对应trace_bit的一个字节 */
	u32 tc_ref; /* Trace bytes ref count            */  //被top_rated引用的次数

	struct queue_entry *next , /* Next element, if any             */
					*next_100; /* 100 elements ahead               */
#ifdef XIAOSA
	u32 parent_id; /* the parent test case id*/
	u32 self_id; /* the self test case id*/
	u8*	change_op; /* mark the change operate*/
	u32 nm_child; /* count the child number*/
	u32 nm_crash_child; /* count the crash child number*/
	u8* fuzz_one_time; /*the time of function of fuzzone, in the level of second*/
	u8 	in_top_rate; /*to mark the testcase is in the top_rate*/
	u8 	has_in_trace_plot;   /*to mark if it has been save in plot file*/
	u8 	kill_signal; /*save the signal value if it has, 0 means no*/
#endif

};

static struct queue_entry *queue , /* Fuzzing queue (linked list)      */
*queue_cur , /* Current offset within the queue  */
*queue_top , /* Top of the list                  */  //指向最新添加的测试用例
		*q_prev100; /* Previous 100 marker              */

static struct queue_entry* top_rated [ MAP_SIZE ]; /* Top entries for bitmap bytes     */

struct extra_data
{
	u8* data; /* Dictionary token data            */
	u32 len; /* Dictionary token length          */
	u32 hit_cnt; /* Use count in the corpus          */
};

static struct extra_data* extras; /* Extra tokens to fuzz with        */
static u32 extras_cnt; /* Total number of tokens read      */

static struct extra_data* a_extras; /* Automatically selected extras    */
static u32 a_extras_cnt; /* Total number of tokens available */

static u8* (*post_handler)(u8* buf, u32* len);

/* Interesting values, as per config.h */

static s8 interesting_8 [ ] =
{ INTERESTING_8 }; //每个是1个字节
static s16 interesting_16 [ ] =
{ INTERESTING_8, INTERESTING_16 }; //每个是2个字节
static s32 interesting_32 [ ] =
{ INTERESTING_8, INTERESTING_16, INTERESTING_32 }; //每个是4个字节

/* Fuzzing stages */

enum
{
	/* 00 */STAGE_FLIP1,			//Single walking bit
	/* 01 */STAGE_FLIP2,		   //Two walking bytes
	/* 02 */STAGE_FLIP4,		   //Four walking bits
	/* 03 */STAGE_FLIP8,		   // Walking byte
	/* 04 */STAGE_FLIP16,       //two walking bytes
	/* 05 */STAGE_FLIP32,       //Four walking bytes
	/* 06 */STAGE_ARITH8,
	/* 07 */STAGE_ARITH16,
	/* 08 */STAGE_ARITH32,
	/* 09 */STAGE_INTEREST8,
	/* 10 */STAGE_INTEREST16,
	/* 11 */STAGE_INTEREST32,
	/* 12 */STAGE_EXTRAS_UO,
	/* 13 */STAGE_EXTRAS_UI,
	/* 14 */STAGE_EXTRAS_AO,
	/* 15 */STAGE_HAVOC,
	/* 16 */STAGE_SPLICE
};

/* Stage value types */

enum
{
	/* 00 */STAGE_VAL_NONE,
	/* 01 */STAGE_VAL_LE, //小端
	/* 02 */STAGE_VAL_BE  //大端模式
};

/* Execution status fault codes */

enum
{
	/* 00 */FAULT_NONE,		//testcase do not crash
	/* 01 */FAULT_HANG,		//testcase results in a hang
	/* 02 */FAULT_CRASH,		//testcase results in a crash
	/* 03 */FAULT_ERROR,		//unable to execute target application
	/* 04 */FAULT_NOINST,	//no instrumentation detected
	/* 05 */FAULT_NOBITS     //no new instrumentation output
};



/* Get unix time in milliseconds */

static u64 get_cur_time(void)
{ //毫秒

	struct timeval tv;
	struct timezone tz;

	gettimeofday(&tv,&tz);\

#ifndef XIAOSA
	return (tv.tv_sec * 1000ULL) + (tv.tv_usec / 1000)
#else
	return (tv.tv_sec * 1000ULL) + (tv.tv_usec / 1000)- (main_start_time/1000);
#endif
}

/* Get unix time in microseconds */ //微秒
static u64 get_cur_time_us(void)
{

	struct timeval tv;
	struct timezone tz;

	gettimeofday(&tv,&tz); //系统api,获取时间

#ifndef XIAOSA
	return (tv.tv_sec * 1000000ULL) + tv.tv_usec
#else
	return (tv.tv_sec * 1000000ULL) + tv.tv_usec- (main_start_time/1000);
#endif
}

/* Generate a random number (from 0 to limit - 1). This may
 have slight bias(偏差). */

static inline u32 UR(u32 limit)
{

	if (!rand_cnt--)
	{

		u32 seed [ 2 ];

		ck_read(dev_urandom_fd,&seed,sizeof(seed),"/dev/urandom"); //读取一个随机数

		srandom(seed [ 0 ]); //应该是读取,在random函数中使用
		rand_cnt = (RESEED_RNG / 2) + (seed [ 1 ] % RESEED_RNG);

	}

	return random() % limit;

}

#ifndef IGNORE_FINDS

/* Helper function to compare buffers; returns first and last differing offset. We
 use this to find reasonable locations for splicing two files. */

static void locate_diffs(u8* ptr1, u8* ptr2, u32 len, s32* first, s32* last)
{

	s32 f_loc = -1;
	s32 l_loc = -1;
	u32 pos;

	for (pos = 0; pos < len; pos++)
	{

		if (*(ptr1++) != *(ptr2++))
		{

			if (f_loc == -1)
				f_loc = pos;
			l_loc = pos;

		}

	}

	*first = f_loc;
	*last = l_loc;

	return;

}

#endif /* !IGNORE_FINDS */

/* Describe integer. Uses 12 cyclic static buffers for return values. The value
 returned should be five characters or less for all the integers we reasonably
 expect to see. */

static u8* DI(u64 val)
{

	static u8 tmp [ 12 ] [ 16 ];
	static u8 cur;

	cur = (cur + 1) % 12;

#define CHK_FORMAT(_divisor, _limit_mult, _fmt, _cast) do { \
    if (val < (_divisor) * (_limit_mult)) { \
      sprintf(tmp[cur], _fmt, ((_cast)val) / (_divisor)); \
      return tmp[cur]; \
    } \
  } while (0)

	/* 0-9999 */
	CHK_FORMAT(1,10000,"%llu",u64);

	/* 10.0k - 99.9k */
	CHK_FORMAT(1000,99.95,"%0.01fk",double);

	/* 100k - 999k */
	CHK_FORMAT(1000,1000,"%lluk",u64);

	/* 1.00M - 9.99M */
	CHK_FORMAT(1000 * 1000,9.995,"%0.02fM",double);

	/* 10.0M - 99.9M */
	CHK_FORMAT(1000 * 1000,99.95,"%0.01fM",double);

	/* 100M - 999M */
	CHK_FORMAT(1000 * 1000,1000,"%lluM",u64);

	/* 1.00G - 9.99G */
	CHK_FORMAT(1000LL * 1000 * 1000,9.995,"%0.02fG",double);

	/* 10.0G - 99.9G */
	CHK_FORMAT(1000LL * 1000 * 1000,99.95,"%0.01fG",double);

	/* 100G - 999G */
	CHK_FORMAT(1000LL * 1000 * 1000,1000,"%lluG",u64);

	/* 1.00T - 9.99G */
	CHK_FORMAT(1000LL * 1000 * 1000 * 1000,9.995,"%0.02fT",double);

	/* 10.0T - 99.9T */
	CHK_FORMAT(1000LL * 1000 * 1000 * 1000,99.95,"%0.01fT",double);

	/* 100T+ */
	strcpy(tmp [ cur ],"infty");
	return tmp [ cur ];

}

/* Describe float. Similar to the above, except with a single 
 static buffer. */

static u8* DF(double val)
{

	static u8 tmp [ 16 ];

	if (val < 99.995)
	{
		sprintf(tmp,"%0.02f",val);
		return tmp;
	}

	if (val < 999.95)
	{
		sprintf(tmp,"%0.01f",val);
		return tmp;
	}

	return DI((u64) val);

}

/* Describe integer as memory size. */

static u8* DMS(u64 val)
{

	static u8 tmp [ 12 ] [ 16 ];
	static u8 cur;

	cur = (cur + 1) % 12;

	/* 0-9999 */
	CHK_FORMAT(1,10000,"%llu B",u64);

	/* 10.0k - 99.9k */
	CHK_FORMAT(1024,99.95,"%0.01f kB",double);

	/* 100k - 999k */
	CHK_FORMAT(1024,1000,"%llu kB",u64);

	/* 1.00M - 9.99M */
	CHK_FORMAT(1024 * 1024,9.995,"%0.02f MB",double);

	/* 10.0M - 99.9M */
	CHK_FORMAT(1024 * 1024,99.95,"%0.01f MB",double);

	/* 100M - 999M */
	CHK_FORMAT(1024 * 1024,1000,"%llu MB",u64);

	/* 1.00G - 9.99G */
	CHK_FORMAT(1024LL * 1024 * 1024,9.995,"%0.02f GB",double);

	/* 10.0G - 99.9G */
	CHK_FORMAT(1024LL * 1024 * 1024,99.95,"%0.01f GB",double);

	/* 100G - 999G */
	CHK_FORMAT(1024LL * 1024 * 1024,1000,"%llu GB",u64);

	/* 1.00T - 9.99G */
	CHK_FORMAT(1024LL * 1024 * 1024 * 1024,9.995,"%0.02f TB",double);

	/* 10.0T - 99.9T */
	CHK_FORMAT(1024LL * 1024 * 1024 * 1024,99.95,"%0.01f TB",double);

#undef CHK_FORMAT

	/* 100T+ */
	strcpy(tmp [ cur ],"infty");
	return tmp [ cur ];

}

/* Describe time delta. Returns one static buffer, 34 chars of less. */

static u8* DTD(u64 cur_ms, u64 event_ms) //第一个参数是结束时间(毫秒),第二个参数是开始时间(毫秒)
{

	static u8 tmp [ 64 ];
	u64 delta;
	s32 t_d , t_h , t_m , t_s;

	if (!event_ms)
		return "none seen yet";

	delta = cur_ms - event_ms;

	t_d = delta / 1000 / 60 / 60 / 24;
	t_h = (delta / 1000 / 60 / 60) % 24;
	t_m = (delta / 1000 / 60) % 60;
	t_s = (delta / 1000) % 60;

	sprintf(tmp,"%s days, %u hrs, %u min, %u sec",DI(t_d),t_h,t_m,t_s);
	return tmp;

}

/* Mark deterministic checks as done for a particular queue entry. We use the
 .state file to avoid repeating deterministic fuzzing when resuming aborted
 scans. */

static void mark_as_det_done(struct queue_entry* q)
{

	u8* fn = strrchr(q->fname,'/');
	s32 fd;

	fn = alloc_printf("%s/queue/.state/deterministic_done/%s",out_dir,fn + 1);

	fd = open(fn,O_WRONLY | O_CREAT | O_EXCL,0600);
	if (fd < 0)
		PFATAL("Unable to create '%s'",fn);
	close(fd);

	ck_free(fn);

	q->passed_det = 1;

}

/* Mark as variable. Create symlinks if possible to make it easier to examine
 the files. */

static void mark_as_variable(struct queue_entry* q)
{

	u8 *fn = strrchr(q->fname,'/') + 1 , *ldest;

	ldest = alloc_printf("../../%s",fn);
	fn = alloc_printf("%s/queue/.state/variable_behavior/%s",out_dir,fn);

	if (symlink(ldest,fn))
	{

		s32 fd = open(fn,O_WRONLY | O_CREAT | O_EXCL,0600);
		if (fd < 0)
			PFATAL("Unable to create '%s'",fn);
		close(fd);

	}

	ck_free(ldest);
	ck_free(fn);

	q->var_behavior = 1;

}

/* Mark / unmark as redundant (edge-only). This is not used for restoring state,
 but may be useful for post-processing datasets. */

static void mark_as_redundant(struct queue_entry* q, u8 state)
{ //将冗余的测试用例保存

	u8* fn;
	s32 fd;
#ifdef XIAOSA
	u8 * tmpy;
	s32 fdy;
	s32 ylen;
#endif

	if (state == q->fs_redundant)
		return; //这里表示一个条件,可能都为1

	q->fs_redundant = state;

	fn = strrchr(q->fname,'/');
	fn = alloc_printf("%s/queue/.state/redundant_edges/%s",out_dir,fn + 1); //+1表示去掉斜杠

	if (state)
	{

		fd = open(fn,O_WRONLY | O_CREAT | O_EXCL,0600);
		if (fd < 0)
			PFATAL("Unable to create '%s'",fn);
		close(fd);

#ifdef XIAOSA
		//open the file
		tmpy = alloc_printf("%s/redundant_edges",out_dir);
		fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600);
		if (fdy < 0)
			PFATAL("Unable to create '%s'",tmpy);
		ck_free(tmpy);
		//write something to the file
		tmpy = strrchr(q->fname,'/'); //表示文件名
		tmpy = alloc_printf(
				"%-54s is not favorated, and its bitmapsize is %-6u \n",
				tmpy + 1,q->bitmap_size);
		ylen = snprintf(NULL,0, "%s",tmpy);
		ck_write(fdy,tmpy,ylen,"redundant_edges");
		ck_free(tmpy);
		close(fdy);

#endif

	}
	else
	{

#ifdef XIAOSA
		//open the file
		tmpy = alloc_printf("%s/redundant_resume",out_dir);
		fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600);
		if (fdy < 0)
			PFATAL("Unable to create '%s'",tmpy);
		ck_free(tmpy);

		tmpy =
				alloc_printf(
						"%s favor again, and its bit_map size is %u\n",
						q->fname,q->bitmap_size);

		ylen = snprintf(NULL,0,"%s",tmpy);
		ck_write(fdy,tmpy,ylen,"redundant_resume");
		ck_free(tmpy);
		close(fdy);
#endif
		if (unlink(fn))
			PFATAL("Unable to remove '%s'",fn); //不存在就会报错

	}

	ck_free(fn);

}

/* Append new test case to the queue. */

static void add_to_queue(u8* fname, u32 len, u8 passed_det)
{

	struct queue_entry* q = ck_alloc(sizeof(struct queue_entry)); //这里初始化都是0

	q->fname = fname;
	q->len = len;
	q->depth = cur_depth + 1;
	q->passed_det = passed_det;

	if (q->depth > max_depth)
		max_depth = q->depth;

	if (queue_top)
	{

		queue_top->next = q;
		queue_top = q;

	}
	else
		q_prev100 = queue = queue_top = q;

	queued_paths++;
	pending_not_fuzzed++;

	if (!(queued_paths % 100))
	{

		q_prev100->next_100 = q;
		q_prev100 = q;

	}

	last_path_time = get_cur_time();

}

/* Destroy the entire queue. */

static void destroy_queue(void)
{

	struct queue_entry *q = queue , *n;

	while (q)
	{

		n = q->next;
		ck_free(q->fname);
		ck_free(q->trace_mini);
#ifdef XIAOSA
		ck_free(q->change_op);
		ck_free(q->fuzz_one_time);
#endif
		ck_free(q);
		q = n;

	}

}

/* Write bitmap to file. The bitmap is useful mostly for the secret
 -B option, to focus a separate fuzzing session on a particular
 interesting input without rediscovering all the others. */

static void write_bitmap(void)
{

	u8* fname;
	s32 fd;

	if (!bitmap_changed)
		return;
	bitmap_changed = 0;

	fname = alloc_printf("%s/fuzz_bitmap",out_dir);
	fd = open(fname,O_WRONLY | O_CREAT | O_TRUNC,0600);

	if (fd < 0)
		PFATAL("Unable to open '%s'",fname);

	ck_write(fd,virgin_bits,MAP_SIZE,fname);

	close(fd);
	ck_free(fname);

}

/* Read bitmap from file. This is for the -B option again. */

static void read_bitmap(u8* fname)
{

	s32 fd = open(fname,O_RDONLY);

	if (fd < 0)
		PFATAL("Unable to open '%s'",fname);

	ck_read(fd,virgin_bits,MAP_SIZE,fname);

	close(fd);

}

/* Check if the current execution path brings anything new to the table.
 Update virgin bits to reflect the finds. Returns 1 if the only change is
 the hit-count for a particular tuple; 2 if there are new tuples seen.
 Updates the map, so subsequent calls will always return 0.

 This function is called after every exec() on a fairly large buffer, so
 it needs to be fast. We do this in 32-bit and 64-bit flavors. */

#define FFL(_b) (0xffULL << ((_b) << 3))  //UUL is unsigned long long 64位
#define FF(_b)  (0xff << ((_b) << 3)) //0xff*2^(_b*8)

static inline u8 has_new_bits(u8* virgin_map)
{

#ifdef __x86_64__

	u64* current = (u64*)trace_bits; //单个  //0表示没有,1表示有  //包含滚筒值
	u64* virgin = (u64*)virgin_map; //总和   //1表示没有,0表示有  //包含滚筒值

	u32 i = (MAP_SIZE >> 3); // 8个字节一次,一共处理 2^13=8192次,共计65536个字节

#else

	u32* current = (u32*) trace_bits;
	u32* virgin = (u32*) virgin_map;

	u32 i = (MAP_SIZE >> 2);

#endif /* ^__x86_64__ */

	u8 ret = 0;

	while (i--)
	{

#ifdef __x86_64__

		u64 cur = *current;
		u64 vir = *virgin;

#else

		u32 cur = *current;
		u32 vir = *virgin; //这个初始所有位全是1

#endif /* ^__x86_64__ */

		/* Optimize for *current == ~*virgin, since this will almost always be the
		 case. */

		if (cur & vir)
		{  //判断当前的元组关系(考虑滚筒)是否出现过,没有出现过进入循环

			if (ret < 2)
			{ //ret 初始为0 ,一旦为2后一直不进入这个判断

				/* This trace did not have any new bytes yet; see if there's any
				 current[] byte that is non-zero when virgin[] is 0xff. */

#ifdef __x86_64__  //8个字节(8个元组关系)处理一次 为了提高效率
				//判断逻辑是   [ (cur & FFL(0)  ] && [   vir & FFL(0)  ] == FFL(0)
				//==的优先级高于&&
				if (    (  (cur & FFL(0) ) && ( vir & FFL(0) ) == FFL(0)  ) ||
						((cur & FFL(1)) && (vir & FFL(1)) == FFL(1)) ||
						((cur & FFL(2)) && (vir & FFL(2)) == FFL(2)) ||
						((cur & FFL(3)) && (vir & FFL(3)) == FFL(3)) ||
						((cur & FFL(4)) && (vir & FFL(4)) == FFL(4)) ||
						((cur & FFL(5)) && (vir & FFL(5)) == FFL(5)) ||
						((cur & FFL(6)) && (vir & FFL(6)) == FFL(6)) ||
						((cur & FFL(7)) && (vir & FFL(7)) == FFL(7))
					)
				//即判断cur的当前字节是否大于0   和   vir的当前字节是否为全1  来判断  当前元组是否为全新的元组
				//vir的当前字节是否为全1表示当前元组关系还没有出现过
				//cur的当前字节是否大于0表示本次测试用例执行到了当前元组
				ret = 2;//表示有新的元组关系出现,至少一个
				else ret = 1;//没有新的元组关系,但是新的滚筒值

#else

				if (	   ((cur & FF(0)) && (vir & FF(0)) == FF(0))
						|| ((cur & FF(1)) && (vir & FF(1)) == FF(1))
						|| ((cur & FF(2)) && (vir & FF(2)) == FF(2))
						|| ((cur & FF(3)) && (vir & FF(3)) == FF(3))
					)
					ret = 2; //第一次出现该元组关系
				else
					ret = 1; //第二次出现该元组关系

#endif /* ^__x86_64__ */

			}

			*virgin = vir & ~cur; //vir是64位,cur是64位,操作后virgin存在0  记录新的元组关系

		}

		current++;
		virgin++;

	}

	if (ret && virgin_map == virgin_bits)
		bitmap_changed = 1; //只要新的元组关系(考虑滚筒)就bitmap更新

	return ret;

}

/* Count the number of bits set in the provided bitmap. Used for the status
 screen several times every second, does not have to be fast. */

static u32 count_bits(u8* mem)
{ //统计mem中的1的位数

	u32* ptr = (u32*) mem;
	u32 i = (MAP_SIZE >> 2); //16384次
	u32 ret = 0;

	while (i--)
	{

		u32 v = *(ptr++);

		/* This gets called on the inverse, virgin bitmap; optimize for sparse
		 data. */

		if (v == 0xffffffff)
		{
			ret += 32;
			continue;
		}

		v -= ((v >> 1) & 0x55555555);
		v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
		ret += (((v + (v >> 4)) & 0xF0F0F0F) * 0x01010101) >> 24;

	}

	return ret;

}

/* Count the number of bytes set in the bitmap. Called fairly sporadically,
 mostly to update the status screen or calibrate and examine confirmed
 new paths. */
//统计非0
static u32 count_bytes(u8* mem)
{ //统计trace_bits 中非0的字节数,即命中的元组的数量

	u32* ptr = (u32*) mem;
	u32 i = (MAP_SIZE >> 2);  //2^14个字节  4个字节处理一次
	u32 ret = 0;

	while (i--)
	{

		u32 v = *(ptr++);

		if (!v)
			continue;
		if (v & FF(0))
			ret++; //FF(0) is 0xff
		if (v & FF(1))
			ret++; //FF(1) is 0xff00
		if (v & FF(2))
			ret++; //FF(2) is 0xff0000
		if (v & FF(3))
			ret++; //FF(3) is 0xff000000

	}

	return ret; //

}

/* Count the number of non-255 bytes set in the bitmap. Used strictly for the
 status screen, several calls per second or so. */
//统计非全1
static u32 count_non_255_bytes(u8* mem)
{ //没有考虑滚筒策略,统计virgin_bit中出现过的元组关系数量

	u32* ptr = (u32*) mem;
	u32 i = (MAP_SIZE >> 2);
	u32 ret = 0;

	while (i--)
	{

		u32 v = *(ptr++);

		/* This is called on the virgin bitmap, so optimize for the most likely
		 case. */

		if (v == 0xffffffff)
			continue;
		if ((v & FF(0)) != FF(0))
			ret++;
		if ((v & FF(1)) != FF(1))
			ret++;
		if ((v & FF(2)) != FF(2))
			ret++;
		if ((v & FF(3)) != FF(3))
			ret++;

	}

	return ret;

}

/* Destructively simplify trace by eliminating hit count information
 and replacing it with 0x80 or 0x01 depending on whether the tuple
 is hit or not. Called on every new crash or hang, should be
 reasonably fast. */

#define AREP4(_sym)   (_sym), (_sym), (_sym), (_sym)
#define AREP8(_sym)   AREP4(_sym), AREP4(_sym)
#define AREP16(_sym)  AREP8(_sym), AREP8(_sym)
#define AREP32(_sym)  AREP16(_sym), AREP16(_sym)
#define AREP64(_sym)  AREP32(_sym), AREP32(_sym)
#define AREP128(_sym) AREP64(_sym), AREP64(_sym)

static u8 simplify_lookup [ 256 ] =
{
/*    4 */1, 128, 128, 128,
/*   +4 */AREP4(128),
/*   +8 */AREP8(128),
/*  +16 */AREP16(128),
/*  +32 */AREP32(128),
/*  +64 */AREP64(128),
/* +128 */AREP128(128) };

#ifdef __x86_64__

static void simplify_trace(u64* mem)
{

	u32 i = MAP_SIZE >> 3;

	while (i--)
	{

		/* Optimize for sparse bitmaps. */

		if (*mem)
		{

			u8* mem8 = (u8*)mem;

			mem8[0] = simplify_lookup[mem8[0]];
			mem8[1] = simplify_lookup[mem8[1]];
			mem8[2] = simplify_lookup[mem8[2]];
			mem8[3] = simplify_lookup[mem8[3]];
			mem8[4] = simplify_lookup[mem8[4]];
			mem8[5] = simplify_lookup[mem8[5]];
			mem8[6] = simplify_lookup[mem8[6]];
			mem8[7] = simplify_lookup[mem8[7]];

		}
		else *mem = 0x0101010101010101ULL;

		mem++;

	}

}

#else

static void simplify_trace(u32* mem)//这个函数的作用,参数一般是trace_bit. 在crash和hang的时候使用
{

	u32 i = MAP_SIZE >> 2; //16384次

	while (i--) //每次处理4个字节,一共16384次,共65536个字节.
	{

		/* Optimize for sparse bitmaps. */

		if (*mem)
		{

			u8* mem8 = (u8*) mem; //初始的mem8 [ i ]表示表示第几个元组关系的执行次数,考虑了滚筒策略

			mem8 [ 0 ] = simplify_lookup [ mem8 [ 0 ] ];
			mem8 [ 1 ] = simplify_lookup [ mem8 [ 1 ] ];
			mem8 [ 2 ] = simplify_lookup [ mem8 [ 2 ] ];
			mem8 [ 3 ] = simplify_lookup [ mem8 [ 3 ] ];

		}
		else
			*mem = 0x01010101; //表示这四个元组关系都没有被击中

		mem++;
	}

}

#endif /* ^__x86_64__ */

/* Destructively classify execution counts in a trace. This is used as a
 preprocessing step for any newly acquired traces. Called on every exec,
 must be fast. */

static u8 count_class_lookup [ 256 ] =
{ //分别是2^1 2^2 2^3...2^8,即字节的每一位表示一个滚筒

		/* 0 - 3:       4 */0, 1, 2, 4,   ///AREP后的值表示个数
				/* 4 - 7:      +4 */AREP4(8),
				/* 8 - 15:     +8 */AREP8(16),
				/* 16 - 31:   +16 */AREP16(32),
				/* 32 - 127:  +96 */AREP64(64), AREP32(64),
				/* 128+:     +128 */AREP128(128)

		};

#ifdef __x86_64__

static inline void classify_counts(u64* mem)
{ //统计各基本块跳跃元组的执行次数,然后归一到滚筒

	u32 i = MAP_SIZE >> 3;//每次操作8个字节,64位,共操作8192次,即65536个元组关系

	while (i--)
	{

		/* Optimize for sparse bitmaps. */

		if (*mem)
		{

			u8* mem8 = (u8*)mem;  //这里用到了滚筒策略  每次指向一个字节

			mem8[0] = count_class_lookup[mem8[0]];//按字节为单位操作trace_bit,8位最大0-255
			mem8[1] = count_class_lookup[mem8[1]];
			mem8[2] = count_class_lookup[mem8[2]];
			mem8[3] = count_class_lookup[mem8[3]];
			mem8[4] = count_class_lookup[mem8[4]];
			mem8[5] = count_class_lookup[mem8[5]];
			mem8[6] = count_class_lookup[mem8[6]];
			mem8[7] = count_class_lookup[mem8[7]];

		}

		mem++; //每次自加64位

	}

}

#else

static inline void classify_counts(u32* mem)
{

	u32 i = MAP_SIZE >> 2;

	while (i--)
	{

		/* Optimize for sparse bitmaps. */

		if (*mem)
		{

			u8* mem8 = (u8*) mem;

			mem8 [ 0 ] = count_class_lookup [ mem8 [ 0 ] ];
			mem8 [ 1 ] = count_class_lookup [ mem8 [ 1 ] ];
			mem8 [ 2 ] = count_class_lookup [ mem8 [ 2 ] ];
			mem8 [ 3 ] = count_class_lookup [ mem8 [ 3 ] ];

		}

		mem++;

	}

}

#endif /* ^__x86_64__ */

/* Get rid of shared memory (atexit handler). */

static void remove_shm(void)
{

	shmctl(shm_id,IPC_RMID,NULL);  //IPC_RMID 表示删除这一段共享内存
#ifdef XIAOSA
	shmctl(shm_id_virgin_counts,IPC_RMID,NULL);
#endif

}

/* Compact trace bytes into a smaller bitmap. We effectively just drop the
 count information here. This is called only sporadically(偶尔), for some
 new paths. */

static void minimize_bits(u8* dst, u8* src)
{

	u32 i = 0;

	while (i < MAP_SIZE)
	{ //65536次循环

		if (*(src++))
		{
			dst [ i >> 3 ] |= 1 << (i & 7); //i&7就是0到7的循环  //这种计算方式贼快 7 is 0b111

		}
		i++;

	}

}

/* When we bump into a new path, we call this to see if the path appears
 more "favorable" than any of the existing ones. The purpose of the
 "favorables" is to have a minimal set of paths that trigger all the bits
 seen in the bitmap so far, and focus on fuzzing them at the expense of
 the rest.

 The first step of the process is to maintain a list of top_rated[](这个数组) entries
 for every byte in the bitmap. We win that slot if there is no previous
 contender, or if the contender has a more favorable speed x size factor. */

static void update_bitmap_score(struct queue_entry* q)
{ //判断是否将测试用例添加到最优测试用例集合中
//这个函数记录的q->trace_mini中已经删除了滚筒策略的相关信息
	u32 i;
	//yy
	u64 fav_factor = q->exec_us * q->len;
	//u64 fav_factor =  q->len;

	/* For every byte set in trace_bits[], see if there is a previous winner,
	 and how it compares to us. */
	for (i = 0; i < MAP_SIZE; i++) //65536次,每次一个字节.

		if (trace_bits [ i ])
		{ //每个测试轨迹 例运行到该基本块时,比较一个数值,将值最小的testcase记录到top_rated数组中

			if (top_rated [ i ])
			{ //初始默认是0 .static

				/* Faster-executing or smaller test cases are favored. */
				//这里没有考虑滚筒
				if (fav_factor > top_rated [ i ]->exec_us * top_rated [ i ]->len)
					//if (fav_factor > top_rated [ i ]->len)
					continue; //运行时间*测试用例长度

				/* Looks like we're going to win. Decrease ref count for the
				 previous winner, discard its trace_bits[] if necessary. */
				//说着有更好的测试用例
				if (!--top_rated [ i ]->tc_ref)
				{ //--表示自减,如果tc_ref是1,判断为真 之前的测试用例引用次数减1
#ifndef XIAOSA
					//原来是有的
					ck_free(top_rated [ i ]->trace_mini);  //表示这个测试用例没有被引用了
					top_rated [ i ]->trace_mini = 0;
#endif

#ifdef XIAOSA
					q->in_top_rate = 0;
#endif
				}

			}

			/* Insert ourselves as the new winner. */

			top_rated [ i ] = q;
			q->tc_ref++;
#ifdef XIAOSA
			q->in_top_rate = 1;
#endif

			if (!q->trace_mini)
			{
				q->trace_mini = ck_alloc(MAP_SIZE >> 3); //分配一个8192个字节,每位对应trace_bit的一个字节
				minimize_bits(q->trace_mini,trace_bits); //去除了滚筒关系 ,0表示没有元组关系,1表示有
			}

			score_changed = 1; //表示有新的测试用例增加到了top_rate数组中.

		}
#ifdef XIAOSA
	//mayby the testcase is not good ,so his trace_mini is not marked
	//heren mark it
	if (!q->trace_mini)
	{
		q->trace_mini = ck_alloc(MAP_SIZE >> 3); //分配一个8192个字节,每位对应trace_bit的一个字节
		minimize_bits(q->trace_mini,trace_bits); //去除了滚筒关系 ,0表示没有元组关系,1表示有
		q->in_top_rate = 0;
	}
#endif
}

/* The second part of the mechanism discussed above is a routine that
 goes over(检查) top_rated[] entries, and then sequentially(继续) grabs winners for
 previously-unseen bytes (temp_v) and marks them as favored(设置favored变量), at least
 until the next run. The favored entries are given more air time during
 all fuzzing steps. */

static void cull_queue(void)
{ //比较的是元组级别的吧?

	struct queue_entry* q;
	static u8 temp_v [ MAP_SIZE >> 3 ]; //8192个字节
	u32 i;

	if (dumb_mode || !score_changed)
		return; //判断有没有更新最小测试用例

	score_changed = 0;

	memset(temp_v,255,MAP_SIZE >> 3); //8192个字节  全部设1; 1表示该元组关系没有出现过

	queued_favored = 0;
	pending_favored = 0;

	q = queue;

	while (q)
	{ //把所有的q->favored,都设置为0 ,每次都是重新排列,保证每次执行的测试用例都是局部最好的,这是贪婪算法.
		q->favored = 0;
		q = q->next;
	}

	/* Let's see if anything in the bitmap isn't captured in temp_v.
	 If yes, and if it has a top_rated[] contender, let's use it. */

	for (i = 0; i < MAP_SIZE; i++)    //多次循环后,temp_v[i >> 3]不一定为全1了
		if (top_rated [ i ] && (temp_v [ i >> 3 ] & (1 << (i & 7))))
		{ //(temp_v[i >> 3] & (1 << (i & 7))) 表示依次取temp_v[i >> 3]字节中的0到7位
		  //top_rated[i]有值,表示运行到的基本块跳跃的测试用例
		  //(temp_v[i >> 3] & (1 << (i & 7)))为0 ,表示其他测试用例也能运行到这个基本块
		  //i的基本块运行了,并且temp+v[]数组的对应位不为0,temp+v[]数组每一位对应trace_bit的一个字节是否为0
			u32 j = MAP_SIZE >> 3;    //8192次

			/* Remove all bits belonging to the current entry from temp_v. */

			while (j--)  //将top_rated[i]的执行轨加到temp_v中
				if (top_rated [ i ]->trace_mini [ j ]) //trace_mini[j]是top_rated[i]基本块的最优测试用例的执行迹,一个字节8为,表示8个元组关系,每8个元组关系做一次判断
					//top_rated[i]表示运行到这个元组的最优测试用例
					temp_v [ j ] &= ~top_rated [ i ]->trace_mini [ j ]; // ~按位取反后,0表示存在,1表示不存在;与temp_v相与后,temp_v中0表示这个元组关系被执行过,1表示没有
			//temp_v[j]记录了所有测试用例的执行迹
			top_rated [ i ]->favored = 1;      	  	 //代表可以继续测试的测试用例; 有再度恢复的测试用例
			queued_favored++; //总的优秀测试用例数量

			if (!top_rated [ i ]->was_fuzzed)
				pending_favored++; //待测试的执行的测试用例

		}
	//结束循环
	// a new cycle for the all testcase in the queue
	// make a new but empty file in the queue/.state/redundant_edges catalog if the testcase's favored is 0.
	q = queue;
	while (q)
	{
		mark_as_redundant(q,!q->favored);
		q = q->next;
	}

}

/* Configure shared memory and virgin_bits. This is called at startup. */

static void setup_shm(void)
{

	u8* shm_str;

	if (!in_bitmap)
		memset(virgin_bits,255,MAP_SIZE);

	memset(virgin_hang,255,MAP_SIZE);  //所有都赋值1
	memset(virgin_crash,255,MAP_SIZE);

	shm_id = shmget(IPC_PRIVATE,MAP_SIZE,IPC_CREAT | IPC_EXCL | 0600); //IPC_PRIVATE也是一种方法,便于父子进程通信

	if (shm_id < 0)
		PFATAL("shmget() failed");
	//在创建共享内存的时候,就声明了删除共享内存的函数
	atexit(remove_shm);  //atexit注册终止函数,remove_shm是函数名,ok

	shm_str = alloc_printf("%d",shm_id);  //shm_id转化成字符串

	/* If somebody is asking us to fuzz instrumented binaries in dumb mode,
	 we don't want them to detect instrumentation, since we won't be sending
	 fork server commands. This should be replaced with better auto-detection
	 later on, perhaps? */

	if (!dumb_mode)
		setenv(SHM_ENV_VAR,shm_str,1); //在插桩模式下增加环境变量

	ck_free(shm_str);

	trace_bits = shmat(shm_id,NULL,0);

	if (!trace_bits)
		PFATAL("64 kb shmat() failed");


#ifdef XIAOSA
//#if 0
	//creat a shm to count the tuple execution number
	u8* shm_str_y;
//	key_t key;
//
//	int fdy=0;
//	remove("/tmp/afl-shm/virgin_counts");
//	fdy=open("/tmp/afl-shm/virgin_counts",O_WRONLY | O_CREAT | O_EXCL,0600);
//	if (fdy < 0)PFATAL("Unable to create ");
//
//	key = ftok("/tmp/afl-shm/virgin_counts",2); //这里x是子序号,自定义的,必须存在这个文件.
//	if (key == -1)
//	{
//		printf("ftok error:%s\n",strerror(errno));
//		PFATAL("ftok() failed");
//	}
	//65536 long, and the style of the element is u32
	//shm_id_virgin_counts = shmget(key,MAP_SIZE,IPC_CREAT | IPC_EXCL | 0600); //IPC_PRIVATE也是一种方法,便于父子进程通信
	shm_id_virgin_counts = shmget(IPC_PRIVATE,MAP_SIZE*4,IPC_CREAT | IPC_EXCL | 0600);
	if (shm_id_virgin_counts < 0)
		PFATAL("shmget() failed");
	//在创建共享内存的时候,就声明了删除共享内存的函数
	atexit(remove_shm);  //atexit注册终止函数,remove_shm是函数名,ok

	shm_str_y = alloc_printf("%d",shm_id_virgin_counts);  //shm_id转化成字符串

	if (!dumb_mode)
		setenv(VIRGIN_COUNTS,shm_str_y,1); //在插桩模式下增加环境变量,通过环境变量告诉子进程qemu

	ck_free(shm_str_y);

	virgin_counts = shmat(shm_id_virgin_counts,NULL,SHM_RDONLY); //afl是只读模式,SHM_RDONLY表示只读模式

	if (!virgin_counts)
		PFATAL("128 kb shmat() failed");
#endif

}

/* Load postprocessor, if available. */

static void setup_post(void)
{

	void* dh;
	u8* fn = getenv("AFL_POST_LIBRARY");
	u32 tlen = 6;

	if (!fn)
		return;

	ACTF("Loading postprocessor from '%s'...",fn);

	dh = dlopen(fn,RTLD_NOW);
	if (!dh)
		FATAL("%s",dlerror());

	post_handler = dlsym(dh,"afl_postprocess");
	if (!post_handler)
		FATAL("Symbol 'afl_postprocess' not found.");

	/* Do a quick test. It's better to segfault now than later =) */

	post_handler("hello",&tlen);

	OKF("Postprocessor installed successfully.");

}

/* Read all testcases from the input directory, then queue them for testing.
 Called at startup. */

static void read_testcases(void)
{

	struct dirent **nl; //namelist
	s32 nl_cnt;
	u32 i;
	u8* fn;

	/* Auto-detect non-in-place resumption attempts. */

	fn = alloc_printf("%s/queue",in_dir);
	if (!access(fn,F_OK))
		in_dir = fn; //F_OK判断是否存在
	else
		ck_free(fn);

	ACTF("Scanning '%s'...",in_dir);

	/* We use scandir() + alphasort() rather than readdir() because otherwise,
	 the ordering  of test cases would vary somewhat randomly and would be
	 difficult to control. */

	nl_cnt = scandir(in_dir,&nl,NULL,alphasort); //扫描in_dir下满足过滤条件的,alphasort是一种排序函数
	//这里还包括 . 和.. 两个目录
	if (nl_cnt < 0)
	{

		if (errno == ENOENT || errno == ENOTDIR)

			SAYF(
					"\n" cLRD "[-] " cRST "The input directory does not seem to be valid - try again. The fuzzer needs\n" "    one or more test case to start with - ideally, a small file under 1 kB\n" "    or so. The cases must be stored as regular files directly in the input\n" "    directory.\n");

		PFATAL("Unable to open '%s'",in_dir);

	}

	for (i = 0; i < nl_cnt; i++)
	{

		struct stat st;

		u8* fn = alloc_printf("%s/%s",in_dir,nl [ i ]->d_name);
		u8* dfn = alloc_printf("%s/.state/deterministic_done/%s",in_dir,
				nl [ i ]->d_name);

		u8 passed_det = 0;

		free(nl [ i ]); /* not tracked */

		if (lstat(fn,&st) || access(fn,R_OK))
			PFATAL("Unable to access '%s'",fn);

		/* This also takes care of . and .. */

		if (!S_ISREG(st.st_mode) || !st.st_size || strstr(fn,"/README.txt"))
		{
			//.  和 .. 目录进入
			ck_free(fn);
			ck_free(dfn);
			continue;

		}

		if (st.st_size > MAX_FILE)
			FATAL("Test case '%s' is too big (%s, limit is %s)",fn,
					DMS(st.st_size),DMS(MAX_FILE));

		/* Check for metadata that indicates that deterministic fuzzing
		 is complete for this entry. We don't want to repeat deterministic
		 fuzzing when resuming aborted scans, because it would be pointless
		 and probably very time-consuming. */

		if (!access(dfn,F_OK))
			passed_det = 1;
		ck_free(dfn);
		//前面的操作都是虚的,目前没有作用
		add_to_queue(fn,st.st_size,passed_det);  //这个函数读取测试用例

	}

	free(nl); /* not tracked */

	if (!queued_paths)
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Looks like there are no valid test cases in the input directory! The fuzzer\n" "    needs one or more test case to start with - ideally, a small file under\n" "    1 kB or so. The cases must be stored as regular files directly in the\n" "    input directory.\n");

		FATAL("No usable test cases in '%s'",in_dir);

	}

	last_path_time = 0;
	queued_at_start = queued_paths;

}

/* Helper function for load_extras. */

static int compare_extras_len(const void* p1, const void* p2)
{
	struct extra_data *e1 = (struct extra_data*) p1 , *e2 =
			(struct extra_data*) p2;

	return e1->len - e2->len;
}

static int compare_extras_use_d(const void* p1, const void* p2)
{
	struct extra_data *e1 = (struct extra_data*) p1 , *e2 =
			(struct extra_data*) p2;

	return e2->hit_cnt - e1->hit_cnt;
}

/* Read extras from a file, sort by size. */

static void load_extras_file(u8* fname, u32* min_len, u32* max_len,
		u32 dict_level)
{

	FILE* f;
	u8 buf [ MAX_LINE ];
	u8 *lptr;
	u32 cur_line = 0;

	f = fopen(fname,"r");

	if (!f)
		PFATAL("Unable to open '%s'",fname);

	while ((lptr = fgets(buf,MAX_LINE,f)))
	{

		u8 *rptr , *wptr;
		u32 klen = 0;

		cur_line++;

		/* Trim on left and right. */

		while (isspace(*lptr))
			lptr++;

		rptr = lptr + strlen(lptr) - 1;
		while (rptr >= lptr && isspace(*rptr))
			rptr--;
		rptr++;
		*rptr = 0;

		/* Skip empty lines and comments. */

		if (!*lptr || *lptr == '#')
			continue;

		/* All other lines must end with '"', which we can consume. */

		rptr--;

		if (rptr < lptr || *rptr != '"')
			FATAL("Malformed name=\"value\" pair in line %u.",cur_line);

		*rptr = 0;

		/* Skip alphanumerics and dashes (label). */

		while (isalnum(*lptr) || *lptr == '_')
			lptr++;

		/* If @number follows, parse that. */

		if (*lptr == '@')
		{

			lptr++;
			if (atoi(lptr) > dict_level)
				continue;
			while (isdigit(*lptr))
				lptr++;

		}

		/* Skip whitespace and = signs. */

		while (isspace(*lptr) || *lptr == '=')
			lptr++;

		/* Consume opening '"'. */

		if (*lptr != '"')
			FATAL("Malformed name=\"keyword\" pair in line %u.",cur_line);

		lptr++;

		if (!*lptr)
			FATAL("Empty keyword in line %u.",cur_line);

		/* Okay, let's allocate memory and copy data between "...", handling
		 \xNN escaping, \\, and \". */

		extras = ck_realloc_block(extras,
				(extras_cnt + 1) * sizeof(struct extra_data));

		wptr = extras [ extras_cnt ].data = ck_alloc(rptr - lptr);

		while (*lptr)
		{

			char* hexdigits = "0123456789abcdef";

			switch (*lptr)
			{

				case 1 ... 31 :
				case 128 ... 255 :
					FATAL("Non-printable characters in line %u.",cur_line);

				case '\\' :

					lptr++;

					if (*lptr == '\\' || *lptr == '"')
					{
						*(wptr++) = *(lptr++);
						klen++;
						break;
					}

					if (*lptr != 'x'|| !isxdigit(lptr[1]) || !isxdigit(lptr[2]))
						FATAL("Invalid escaping (not \\xNN) in line %u.",
								cur_line);

					*(wptr++) =
							((strchr(hexdigits,tolower(lptr [ 1 ])) - hexdigits)
									<< 4)
									| (strchr(hexdigits,tolower(lptr [ 2 ]))
											- hexdigits);

					lptr += 3;
					klen++;

					break;

				default :

					*(wptr++) = *(lptr++);
					klen++;

			}

		}

		extras [ extras_cnt ].len = klen;

		if (extras [ extras_cnt ].len > MAX_DICT_FILE)
			FATAL("Keyword too big in line %u (%s, limit is %s)",cur_line,
					DMS(klen),DMS(MAX_DICT_FILE));

		if (*min_len > klen)
			*min_len = klen;
		if (*max_len < klen)
			*max_len = klen;

		extras_cnt++;

	}

	fclose(f);

}

/* Read extras from the extras directory and sort them by size. */

static void load_extras(u8* dir)
{

	DIR* d;
	struct dirent* de;
	u32 min_len = MAX_DICT_FILE , max_len = 0 , dict_level = 0;
	u8* x;

	/* If the name ends with @, extract level and continue. */

	if ((x = strchr(dir,'@')))
	{

		*x = 0;
		dict_level = atoi(x + 1);

	}

	ACTF("Loading extra dictionary from '%s' (level %u)...",dir,dict_level);

	d = opendir(dir);

	if (!d)
	{

		if (errno == ENOTDIR)
		{
			load_extras_file(dir,&min_len,&max_len,dict_level);
			goto check_and_sort;
		}

		PFATAL("Unable to open '%s'",dir);

	}

	if (x)
		FATAL("Dictinary levels not supported for directories.");

	while ((de = readdir(d)))
	{

		struct stat st;
		u8* fn = alloc_printf("%s/%s",dir,de->d_name);
		s32 fd;

		if (lstat(fn,&st) || access(fn,R_OK))
			PFATAL("Unable to access '%s'",fn);

		/* This also takes care of . and .. */
		if (!S_ISREG(st.st_mode) || !st.st_size)
		{

			ck_free(fn);
			continue;

		}

		if (st.st_size > MAX_DICT_FILE)
			FATAL("Extra '%s' is too big (%s, limit is %s)",fn,DMS(st.st_size),
					DMS(MAX_DICT_FILE));

		if (min_len > st.st_size)
			min_len = st.st_size;
		if (max_len < st.st_size)
			max_len = st.st_size;

		extras = ck_realloc_block(extras,
				(extras_cnt + 1) * sizeof(struct extra_data));

		extras [ extras_cnt ].data = ck_alloc(st.st_size);
		extras [ extras_cnt ].len = st.st_size;

		fd = open(fn,O_RDONLY);

		if (fd < 0)
			PFATAL("Unable to open '%s'",fn);

		ck_read(fd,extras [ extras_cnt ].data,st.st_size,fn);

		close(fd);
		ck_free(fn);

		extras_cnt++;

	}

	closedir(d);

	check_and_sort:

	if (!extras_cnt)
		FATAL("No usable files in '%s'",dir);

	qsort(extras,extras_cnt,sizeof(struct extra_data),compare_extras_len);

	OKF("Loaded %u extra tokens, size range %s to %s.",extras_cnt,DMS(min_len),
			DMS(max_len));

	if (max_len > 32)
		WARNF("Some tokens are relatively large (%s) - consider trimming.",
				DMS(max_len));

	if (extras_cnt > MAX_DET_EXTRAS)
		WARNF("More than %u tokens - will use them probabilistically.",
				MAX_DET_EXTRAS);

}

/* Helper function for maybe_add_auto() */

static inline u8 memcmp_nocase(u8* m1, u8* m2, u32 len)
{

	while (len--)
		if (tolower(*(m1++)) ^ tolower(*(m2++)))
			return 1;
	return 0;

}

/* Maybe add automatic extra. */

static void maybe_add_auto(u8* mem, u32 len)
{

	u32 i;

	/* Allow users to specify that they don't want auto dictionaries. */

	if (!MAX_AUTO_EXTRAS || !USE_AUTO_EXTRAS)
		return;

	/* Skip runs of identical bytes. */

	for (i = 1; i < len; i++)
		if (mem [ 0 ] ^ mem [ i ])
			break;

	if (i == len)
		return;

	/* Reject builtin interesting values. */

	if (len == 2)
	{

		i = sizeof(interesting_16) >> 1;

		while (i--)
			if (*((u16*) mem) == interesting_16 [ i ]||
			*((u16*)mem) == SWAP16(interesting_16[i]))
				return;

	}

	if (len == 4)
	{

		i = sizeof(interesting_32) >> 2;

		while (i--)
			if (*((u32*) mem) == interesting_32 [ i ]||
			*((u32*)mem) == SWAP32(interesting_32[i]))
				return;

	}

	/* Reject anything that matches existing extras. Do a case-insensitive
	 match. We optimize by exploiting the fact that extras[] are sorted
	 by size. */

	for (i = 0; i < extras_cnt; i++)
		if (extras [ i ].len >= len)
			break;

	for (; i < extras_cnt && extras [ i ].len == len; i++)
		if (!memcmp_nocase(extras [ i ].data,mem,len))
			return;

	/* Last but not least, check a_extras[] for matches. There are no
	 guarantees of a particular sort order. */

	auto_changed = 1;

	for (i = 0; i < a_extras_cnt; i++)
	{

		if (a_extras [ i ].len == len
				&& !memcmp_nocase(a_extras [ i ].data,mem,len))
		{

			a_extras [ i ].hit_cnt++;
			goto sort_a_extras;

		}

	}

	/* At this point, looks like we're dealing with a new entry. So, let's
	 append it if we have room. Otherwise, let's randomly evict some other
	 entry from the bottom half of the list. */

	if (a_extras_cnt < MAX_AUTO_EXTRAS)
	{

		a_extras = ck_realloc_block(a_extras,
				(a_extras_cnt + 1) * sizeof(struct extra_data));

		a_extras [ a_extras_cnt ].data = ck_memdup(mem,len);
		a_extras [ a_extras_cnt ].len = len;
		a_extras_cnt++;

	}
	else
	{

		i = MAX_AUTO_EXTRAS / 2 + UR((MAX_AUTO_EXTRAS + 1) / 2);

		ck_free(a_extras [ i ].data);

		a_extras [ i ].data = ck_memdup(mem,len);
		a_extras [ i ].len = len;
		a_extras [ i ].hit_cnt = 0;

	}

	sort_a_extras:

	/* First, sort all auto extras by use count, descending order. */

	qsort(a_extras,a_extras_cnt,sizeof(struct extra_data),compare_extras_use_d);

	/* Then, sort the top USE_AUTO_EXTRAS entries by size. */

	qsort(a_extras,MIN(USE_AUTO_EXTRAS,a_extras_cnt),sizeof(struct extra_data),
			compare_extras_len);

}

/* Save automatically generated extras. */

static void save_auto(void)
{

	u32 i;

	if (!auto_changed)
		return;
	auto_changed = 0;

	for (i = 0; i < MIN(USE_AUTO_EXTRAS,a_extras_cnt); i++)
	{

		u8* fn = alloc_printf("%s/queue/.state/auto_extras/auto_%06u",out_dir,
				i);
		s32 fd;

		fd = open(fn,O_WRONLY | O_CREAT | O_TRUNC,0600);

		if (fd < 0)
			PFATAL("Unable to create '%s'",fn);

		ck_write(fd,a_extras [ i ].data,a_extras [ i ].len,fn);

		close(fd);
		ck_free(fn);

	}

}

/* Load automatically generated extras. */   //extra是用于固定格式的
static void load_auto(void)
{

	u32 i;

	for (i = 0; i < USE_AUTO_EXTRAS; i++)
	{

		u8 tmp [ MAX_AUTO_EXTRA + 1 ];
		u8* fn = alloc_printf("%s/.state/auto_extras/auto_%06u",in_dir,i);
		s32 fd , len;

		fd = open(fn,O_RDONLY,0600);

		if (fd < 0)
		{

			if (errno != ENOENT)
				PFATAL("Unable to open '%s'",fn);
			ck_free(fn);
			break;

		}

		/* We read one byte more to cheaply detect tokens that are too
		 long (and skip them). */

		len = read(fd,tmp,MAX_AUTO_EXTRA + 1);

		if (len < 0)
			PFATAL("Unable to read from '%s'",fn);

		if (len >= MIN_AUTO_EXTRA && len <= MAX_AUTO_EXTRA)
			maybe_add_auto(tmp,len);

		close(fd);
		ck_free(fn);

	}

	if (i)
		OKF("Loaded %u auto-discovered dictionary tokens.",i);
	else
		OKF("No auto-generated dictionary tokens to reuse.");

}

/* Destroy extras. */

static void destroy_extras(void)
{

	u32 i;

	for (i = 0; i < extras_cnt; i++)
		ck_free(extras [ i ].data);

	ck_free(extras);

	for (i = 0; i < a_extras_cnt; i++)
		ck_free(a_extras [ i ].data);

	ck_free(a_extras);

}

/* Code to fuzz targets across localhost/127.0.0.1/::1 network interface
 * 
 * The network fuzzing code operates in each of two modes depending upon
 * the type of target:
 * 
 * (1) as a "listener" or "server" to fuzz targets that send a request to 
 *     another process and expect a response.  These targets are called
 *     "clients". The relevant functions are network_setup_listener(),
 *     which creates a socket and binds that socket to a (local) port
 *     specified on the command line, and network_listen(), which expects
 *     to receive a packet (UDP) or stream of data (TCP) from the target
 *     and sends a fuzzed response.  This mode is selected using the -L
 *     command line option, together with the -N command line option.
 * 
 * (2) as a "client" to fuzz targets that expect to receive a request from
 *     another process.  These targets are called "servers" or "daemons".
 *     The relevant function is network_send(), which sends a fuzzed
 *     packet (UDP) or stream of data (TCP) to the target.  This mode is
 *     selected using the -N command line option without the -L command
 *     line option.
 * 
 *  */

void network_setup_listener(void)
{
	/* exit if getaddrinfo() did not return address information structures
	 * that match the specification on the command line */
	if (N_results != NULL)
	{
		/* two cases: SOCK_STREAM (for TCP) and SOCK_DGRAM (for UDP) */
		if (N_results->ai_socktype == SOCK_STREAM)
		{
			/* TCP (stream) and connections are used.
			 *
			 * A connection must be established from the target each
			 * time network_listen() is called, and closed after the data are
			 * transfered.  network_setup_listener() creates a stream socket
			 * (with the file descriptor N_fd) and listens for connection requests.
			 * This must be done before a target that expects to connect is executed.
			 * N_myaddr_valid tells the codes that the listening socket has been
			 * setup (and keeps this code from running twice as a safety net).
			 * UDP is connectionless and quite different. See below.
			 *
			 * Local variables: */
			int optval = 1;
			if (N_myaddr_valid == 0)
			{ /* don't do this twice! */
				/* Find the first address that works and use it. */
				for (N_rp = N_results; N_rp != NULL; N_rp = N_rp->ai_next)
				{
					/* create the socket, skipping to the next addrinfo object on failure */
					N_fd = socket(N_rp->ai_family,N_rp->ai_socktype,
							N_rp->ai_protocol);
					if (N_fd == -1)
					{
						close(N_fd);
						continue;
					}
					/* set the socket option to reuse both the address and port */
					if (setsockopt(N_fd,SOL_SOCKET,SO_REUSEADDR | SO_REUSEPORT,
							&optval,sizeof(optval)) == -1)
					{
						close(N_fd);
						PFATAL("failed to set socket option (TCP case)");
					}
					/* if bind() succeeds, we have found an address that works */
					if (bind(N_fd,N_rp->ai_addr,N_rp->ai_addrlen) != -1)
					{
						break;
					}
					close(N_fd);
				}
				/* if none is found, the user needs to examine the argument list */
				if (N_rp == NULL)
				{
					FATAL("failed to bind socket");
				}
				/* listen for connection attempts.  this can fail if another process
				 * is listening to the same port and address */
				if (listen(N_fd,8) == -1)
					PFATAL("listen() failed");
				/* indicate that the socket has been created & bound to a port, and
				 * that the process is listening for connection attempts. */
				N_myaddr_valid = 1;
			}
		}
		else if (N_results->ai_socktype == SOCK_DGRAM)
		{
			/* UDP datagrams are used.
			 *
			 * Create a socket to be used to both receive and send packets, referenced
			 * by the file descriptor N_fd.
			 *
			 * N_fd is kept open for the duration of the afl run (closed on exit)
			 * and reused.  N_myaddr_valid signals the code that the UDP socket
			 * has been set up and bound to the sending side of the address & port.
			 *
			 * First time: find the appropriate sockaddr structure to be used and
			 * set up the sending side's socket. After the first time's successful
			 * execution, N_rp points to the address information corresonding to
			 * the sending side's socket information.
			 *
			 * Local variables:
			 */
			int optval = 1;
			if (N_myaddr_valid == 0)
			{
				for (N_rp = N_results; N_rp != NULL; N_rp = N_rp->ai_next)
				{
					/* create the socket, skipping to the next addrinfo object on failure */
					N_fd = socket(N_rp->ai_family,N_rp->ai_socktype,
							N_rp->ai_protocol);
					if (N_fd == -1)
					{
						fprintf(stderr,"socket() call failed\n");
						close(N_fd);
						continue;
					}
					/* set the socket option to reuse both the address and port */
					if (setsockopt(N_fd,SOL_SOCKET,SO_REUSEADDR | SO_REUSEPORT,
							&optval,sizeof(optval)) == -1)
					{
						close(N_fd);
						PFATAL("failed to set socket option (TCP case)");
					}
					/* if bind() succeeds, we have found an address that works */
					if (bind(N_fd,N_rp->ai_addr,N_rp->ai_addrlen) != -1)
					{
						break;
					}
					close(N_fd);
				}
				/* if none is found, the user needs to examine the argument list */
				if (N_rp == NULL)
				{
					FATAL("failed to bind socket");
				}
				/* indicate that the socket has been created & bound to a port, and
				 * that the process is listening for connection attempts. */
				N_myaddr_valid = 1;
			}
		}
	}
	else
	{
		/* getaddrinfo() failed to return results matching the spec on the
		 * command line.  */
		FATAL("no matching results from getaddrinfo()");
	}
}

int network_listen(void)
{
	/* This function receives data from the target process, and then sends
	 * fuzzed data back to it.  There are two cases:
	 *
	 * (1) TCP (streams): a connection attempt from the target process is
	 *     solicited.  When the connection has been established, all available
	 *     data are read using non-blocking I/O, and then fuzzed data are
	 *     written.
	 *
	 * (2) UDP (datagrams/packets): all available packets are read using
	 *     non-blocking I/O, and then fuzzed data are written.
	 *
	 * In both cases, all data read are discarded.  Note that for UDP reads
	 * any data in excess of the size of the read buffer are discarded by the
	 * network stack.
	 *
	 * Note that non-blocking reads are attempted, and if they fail then the
	 * calling process is expected to wait for a programmed interval of time
	 * (specified by the -D command line argument) and retry the call to
	 * network_listen(), for a programmed number of times (not user-selectable).
	 *
	 * Note that unlike the case where this code plays the role of a client to
	 * the target process (using network_send()), we typically have no control
	 * over the target's reuse (or not) of ephemeral port numbers.  Therefore,
	 * we are at the mercy of the network stack's ability to scavenge available
	 * port numbers.  A recent Linux kernel appears to do this quite well;
	 * other operating systems may not.
	 *
	 * Local variables:
	 */
	u32 MAXRECVBUFSIZE = 512;
	u8 recvbuf [ MAXRECVBUFSIZE ];
	s32 currreadlen , client_fd , fd , o;
	/* network_setup_listener() must be called first, and must succeed */
	if (!N_myaddr_valid)
		FATAL("error: network_listen() called before network_setup_listener()");

	/* Two cases: SOCK_STREAM (for TCP) and SOCK_DGRAM (for UDP) */
	if (N_rp->ai_socktype == SOCK_STREAM)
	{
		/* TCP (stream) and connections are used. */
		/* accept a connection if the client is ready, but don't block */
		client_fd = accept4(N_fd,(struct sockaddr *) &N_myaddr,&N_myaddrlen,
				SOCK_CLOEXEC | SOCK_NONBLOCK);
		if (client_fd == -1)
		{
			if ((errno == EAGAIN) || (errno == EWOULDBLOCK))
			{
				return -1; /* return to calling program, which will delay before retrying */
			}
			else
			{ /* a serous error occurred */
				PFATAL(
						"accept4() returned error other than EAGAIN or EWOULDBLOCK");
			}
		}
		/* read whatever the client sends and throw it away, resetting
		 * non-blocking mode first (because some UNIXs propagate it to
		 * the returned client_fd) */
		o = fcntl(client_fd,F_GETFL);
		if (o >= 0)
		{
			o = o & (~O_NONBLOCK);
			if (fcntl(client_fd,F_SETFL,o) < 0)
			{
				PFATAL(
						"failed to reset non-blocking flag on client file descriptor (TCP)");
			}
		}
		while ((currreadlen = recv(client_fd,recvbuf,MAXRECVBUFSIZE,
				MSG_DONTWAIT)) > 0)
			;
		if ((currreadlen <= 0) && (errno != EAGAIN) && (errno != EWOULDBLOCK))
		{
			PFATAL("read error");
		}
		/* duplicate the file descriptor used for the fuzzed data, and use the new
		 * file descriptor to read that data and send it to the target process */
		fd = dup(out_fd);
		struct stat statbuf;
		/* stat the file descriptor to obtain the size of the data to be sent */
		if (fstat(fd,&statbuf) == -1)
		{
			PFATAL("failed to obtain stat for output file to target");
		}
		/* seek to the beginning of the file */
		lseek(fd,0,SEEK_SET);
		/* use sendfile() to transfer the data if possible because it is efficient */
		if (sendfile(client_fd,fd,NULL,statbuf.st_size) == -1)
		{
			/* if sendfile() didn't work, use read() and write() via a buffer */
			lseek(fd,0,SEEK_SET); /* reset to the beginning of the file */
			u8 tempbuf [ 512 ];
			u32 kread;
			while ((kread = read(fd,tempbuf,512)) > 0)
			{
				if (write(client_fd,tempbuf,kread) != kread)
				{
					PFATAL("file copy to network socket failed (TCP)");
				}
			}
		}
		/* leave a clean campsite (as we found it) */
		lseek(fd,0,SEEK_SET);
		close(fd);
		/* and close the file descriptor of the socket for the target */
		close(client_fd);

	}
	else if (N_rp->ai_socktype == SOCK_DGRAM)
	{
		/* UDP datagrams are used.
		 *
		 * N_fd is kept open for the duration of the afl run (closed on exit)
		 * and reused.  N_myaddr_valid signals this code that the UDP socket
		 * has been set up and bound to the sending side of the address & port.
		 * N_rp points to the address information used for the socket.
		 *
		 * Local variables:
		 */
		struct stat statbuf;
		struct sockaddr_storage clientaddr;
		u32 clientaddrlen = sizeof(struct sockaddr_storage);
		/* read all available packets from the socket using non-blocking I/O */
		{
			int received_one = 0;
			while ((currreadlen = recvfrom(N_fd,recvbuf,MAXRECVBUFSIZE,
					MSG_DONTWAIT,(struct sockaddr *) &clientaddr,&clientaddrlen))
					> 0)
			{
				received_one = 1;
			}
			/* at least one is necessary; otherwise, return & calling program may
			 * wait and then try again */
			if (!received_one)
			{
				if ((errno == EAGAIN) || (errno == EWOULDBLOCK))
				{
					return -1;
				}
				else
				{
					/* any other error signals imply a serious problem exists */
					PFATAL("read error");
				}
			}
		}
		/* duplicate the file descriptor used for the fuzzed data, and use the new
		 * file descriptor to read that data and send it to the target process */
		fd = dup(out_fd);
		/* stat the file descriptor to obtain the size of the data to be sent */
		if (fstat(fd,&statbuf) == -1)
			PFATAL("fstat()failed");
		/* seek to the beginning of the file and create a temporary buffer to
		 * hold all of the data in the file */
		lseek(fd,0,SEEK_SET);
		u8 tempbuf [ statbuf.st_size ];
		/* read the entire file into the buffer */
		if (read(fd,tempbuf,statbuf.st_size) != statbuf.st_size)
			PFATAL(
					"read of outfile's content failed to return expected # of bytes");
		/* and send the buffer's content to the target process.  Note that this
		 * code assumes that the entire buffer can be sent in a single packet.  If
		 * it can not (giant packet), the user may be doing something wrong.  */
		if (sendto(N_fd,tempbuf,statbuf.st_size,0,
				(struct sockaddr *) &clientaddr,clientaddrlen) < 0)
		{
			PFATAL("partial or failed UDP write");
		}
		/* leave a clean campsite (as we found it) */
		lseek(fd,0,SEEK_SET);
		close(fd);
	}
	return 0;
}

int network_send(void)
{
	/* This function sends fuzzed data to a target process.  There are two cases:
	 *
	 * (1) TCP (streams): a connection to the target process is attempted.
	 *     When the connection has been established, the fuzzed data are
	 *     written.
	 *
	 * (2) UDP (datagrams/packets): The fuzzed data are written.
	 *
	 * N_results should never be a NULL pointer because the return code
	 * from getaddrinfo() is checked. */
	if (N_results != NULL)
	{

		/* Two cases: SOCK_STREAM (for TCP) and SOCK_DGRAM (for UDP) */
		if (N_results->ai_socktype == SOCK_STREAM)
		{
			/* TCP (stream) and connections are used.
			 *
			 * NOTE: A TCP connection must be established each time this code
			 * is called, and closed after the data are transfered.  However, the
			 * same port number should be used for the sending (this) side of the
			 * TCP transaction every time.  Otherwise, ephemeral port
			 * numbers might be exhausted because of TCP's TIME_WAIT timeout
			 * interval.  N_myaddr_valid tells this code that the sending side's
			 * address information has been stored in N_myaddr and is to be reused.
			 * UDP is connectionless and is therefore different. See below.
			 *
			 * Note that the other mode of operation, where this code acts as a
			 * server to a target, does not have control over the target's reuse
			 * of ephemeral port numbers.  See the comments in network_listen()
			 * for a discussion.
			 *
			 * Note that "soft" failures cause a return with an error code of -1. The
			 * calling process is expected to wait for a programmed interval of time
			 * (specified by the -D command line argument) and retry the call to
			 * network_send(), for a programmed number of times (not user-selectable)
			 * when this occurs.
			 *
			 * Local variables: */
			int optval = 1;

			if (N_myaddr_valid == 0)
			{
				/* First time: Find the correct address and use it, saving the info
				 * in M_myaddr for subsequent calls. */
				for (N_rp = N_results; N_rp != NULL; N_rp = N_rp->ai_next)
				{
					/* create a socket to connect to the target process */
					N_fd = socket(N_rp->ai_family,N_rp->ai_socktype,
							N_rp->ai_protocol);
					if (N_fd == -1)
					{
						continue;
					}
					/* set the socket options to reuse both the address and port */
					if (setsockopt(N_fd,SOL_SOCKET,SO_REUSEADDR | SO_REUSEPORT,
							&optval,sizeof(optval)) == -1)
					{
						PFATAL("failed to set socket option (TCP case)");
					}
					/* attempt to connect to the target process, breaking out of the
					 * loop upon success */
					if (connect(N_fd,N_rp->ai_addr,N_rp->ai_addrlen) != -1)
					{
						break;
					}
					/* connect() failed, so close the file descriptor and try the
					 * next address information data structure */
					close(N_fd);
				}
				if (N_rp == NULL)
				{
					return -1; /* failed to connect; target process probably not ready */
				}
				/* obtain the send side socket information for re-use */
				if (getsockname(N_fd,(struct sockaddr *) (&N_myaddr),
						&N_myaddrlen) == -1)
				{
					PFATAL(
							"unable to obtain local socket address information (TCP case)");
				}
				N_myaddr_valid = 1;
			}
			else
			{
				/* This is not the first time; reuse send side info in N_myaddr. */
				N_fd = socket(N_rp->ai_family,N_rp->ai_socktype,
						N_rp->ai_protocol);
				if (N_fd == -1)
				{
					PFATAL(
							"Subsequent attempt to create socket failed (TCP case)");
				}
				if (setsockopt(N_fd,SOL_SOCKET,SO_REUSEADDR | SO_REUSEPORT,
						&optval,sizeof(optval)) == -1)
				{
					PFATAL(
							"Subsequent attempt to set socket option failed (TCP case)");
				}
				if (bind(N_fd,(struct sockaddr *) (&N_myaddr),N_myaddrlen)
						== -1)
				{
					PFATAL(
							"Attempt to bind socket to source address & port failed (TCP case)");
				}
				if (connect(N_fd,N_rp->ai_addr,N_rp->ai_addrlen) != -1)
				{
				}
				else
				{
					close(N_fd);
					return -1; /* error returned from connect; target process not ready */
				}
			}

			{
				/* duplicate the file descriptor used for the fuzzed data, and use
				 * the new file descriptor to read that data and send it to the
				 * target process */
				s32 fd = dup(out_fd);
				/* stat the file descriptor to obtain the size of the data to be sent */
				struct stat statbuf;
				if (fstat(fd,&statbuf) == -1)
					PFATAL("fstat()failed");
				/* seek to the beginning of the file */
				lseek(fd,0,SEEK_SET);
				/* use sendfile() to transfer the data if possible because it is efficient */
				if (sendfile(N_fd,fd,NULL,statbuf.st_size) == -1)
				{
					/* if sendfile() didn't work, use read() and write() via a buffer */
					lseek(fd,0,SEEK_SET); /* reset to the beginning of the file */
					/* create a temporary buffer to hold all of the data in the file */
					u8 tempbuf [ 512 ];
					u32 kread;
					while ((kread = read(fd,tempbuf,512)) > 0)
					{
						if (write(N_fd,tempbuf,kread) != kread)
						{
							PFATAL("file copy to network socket failed (TCP)");
						}
					}
				}
				/* leave a clean campsite (as we found it) */
				lseek(fd,0,SEEK_SET);
				close(fd);
			}
			/* and close the connection to the target process, signaling EOF */
			close(N_fd);

		}
		else if (N_results->ai_socktype == SOCK_DGRAM)
		{
			/* UDP datagrams are used.
			 *
			 * N_fd is kept open for the duration of the afl run (closed on exit)
			 * and reused.  N_myaddr_valid signals this code that the UDP socket
			 * has been set up and bound to the sending side of the address & port.
			 * N_rp points to the recipient side's address information after the
			 * first call. */

			if (N_myaddr_valid == 0)
			{
				/* First time: find the appropriate sockaddr structure to be used and
				 * set up the sending side's socket. After the first time's successful
				 * execution, N_myaddr holds the sending side's socket information,
				 * N_rp points to the socket address structure that was used to
				 * create the socket, and N_fd is a valid file descriptor for the
				 * socket. */
				for (N_rp = N_results; N_rp != NULL; N_rp = N_rp->ai_next)
				{
					if (!((N_rp->ai_family == AF_INET)
							|| (N_rp->ai_family == AF_INET6)))
					{
						continue;
					}
					/* create appropriate struct sockaddr according to ai_family */
					if (N_rp->ai_family == AF_INET6)
					{
						memset(&N_server_addr,0,sizeof(struct sockaddr_in6));
						N_server_addr.ss_family = AF_INET6;
						((struct sockaddr_in6 *) &N_server_addr)->sin6_family =
						AF_INET6;
						((struct sockaddr_in6 *) &N_server_addr)->sin6_addr =
								in6addr_any;
						((struct sockaddr_in6 *) &N_server_addr)->sin6_port = 0;
					}
					else if (N_rp->ai_family == AF_INET)
					{
						memset(&N_server_addr,0,sizeof(struct sockaddr_in));
						N_server_addr.ss_family = AF_INET;
						((struct sockaddr_in *) &N_server_addr)->sin_family =
						AF_INET;
						((struct sockaddr_in *) &N_server_addr)->sin_addr.s_addr =
						INADDR_ANY;
						((struct sockaddr_in *) &N_server_addr)->sin_port = 0;
					}
					else
					{
						FATAL("invalid ai_family (UDP case)");
					}
					/* create socket */
					N_fd = socket(N_rp->ai_family,N_rp->ai_socktype,
							N_rp->ai_protocol);
					if (N_fd == -1)
					{
						continue;
					}
					/* bind to the address using an ephemeral port number */
					if (bind(N_fd,(struct sockaddr *) &N_server_addr,
							sizeof(struct sockaddr_storage)) < 0)
					{
						PFATAL("bind failed (UDP case)");
					}
					else
					{
						/* obtain the local port number that was assigned (for debugging) */
						N_myaddrlen = sizeof(struct sockaddr_storage);
						if (getsockname(N_fd,(struct sockaddr *) &N_myaddr,
								&N_myaddrlen) < 0)
						{
							PFATAL("get socket name failed (UDP case)");
						}
						else
						{
							break;
						}
					}
					close(N_fd);
				}
				N_myaddr_valid = 1;
			}
			if (N_rp == NULL)
			{
				return -1; /* failed to connect on any address (UDP case) */
			}
			{
				/* duplicate the file descriptor used for the fuzzed data, and use
				 * the new file descriptor to read that data and send it to the
				 * target process */
				s32 fd = dup(out_fd);
				/* stat the file descriptor to obtain the size of the data to be sent */
				struct stat statbuf;
				if (fstat(fd,&statbuf) == -1)
					PFATAL("fstat()failed");
				/* seek to the beginning of the file */
				lseek(fd,0,SEEK_SET);
				/* create a temporary buffer to hold all of the data in the file */
				u8 tempbuf [ statbuf.st_size ];
				/* read the entire file into the buffer */
				if (read(fd,tempbuf,statbuf.st_size) != statbuf.st_size)
				{
					PFATAL(
							"read of outfile's content failed to return expected # of bytes");
				}
				if (N_rp->ai_family == AF_INET)
				{
					/* and send the buffer's content to the target process.  Note that
					 * this code assumes that the entire buffer can be sent in a single
					 * packet.  If it can not (giant packet), the user may be doing
					 * something wrong.  */
					if (sendto(N_fd,tempbuf,statbuf.st_size,0,
							(struct sockaddr *) ((N_rp)->ai_addr),
							sizeof(struct sockaddr_in)) < 0)
					{
						PFATAL("partial or failed UDP write (IPv4)");
					}
				}
				else if (N_rp->ai_family == AF_INET6)
				{
					if (sendto(N_fd,tempbuf,statbuf.st_size,0,
							(struct sockaddr *) ((N_rp)->ai_addr),
							sizeof(struct sockaddr_in6)) < 0)
					{
						PFATAL("partial or failed UDP write (IPv6)");
					}
				}
				/* leave a clean campsite (as we found it) */
				lseek(fd,0,SEEK_SET);
				close(fd);
			}
		}
	}
	else
	{
		/* this should never be executed */
		FATAL(
				"no address information structures match command line network spec");
	}

	return 0;
}

/* Spin up fork server (instrumented mode only). The idea is explained here:

 http://lcamtuf.blogspot.com/2014/10/fuzzing-binaries-without-execve.html

 In essence, the instrumentation allows us to skip execve(), and just keep
 cloning a stopped child. So, we just execute once, and then send commands
 through a pipe. The other part of this logic is in afl-as.h. */

static void init_forkserver(char** argv)
{

	static struct itimerval it;
	int st_pipe [ 2 ] , ctl_pipe [ 2 ];
	int status;
	s32 rlen;

	ACTF("Spinning up the fork server...");

	if (pipe(st_pipe) || pipe(ctl_pipe))
		PFATAL("pipe() failed");

	forksrv_pid = fork();   //

	if (forksrv_pid < 0)
		PFATAL("fork() failed");

	if (!forksrv_pid)
	{ //child

		struct rlimit r;

		/* Umpf. On OpenBSD, the default fd limit for root users is set to
		 soft 128. Let's try to fix that... */

		if (!getrlimit(RLIMIT_NOFILE,&r) && r.rlim_cur < FORKSRV_FD + 2)
		{

			r.rlim_cur = FORKSRV_FD + 2;
			setrlimit(RLIMIT_NOFILE,&r); /* Ignore errors */

		}

		if (mem_limit)
		{

			r.rlim_max = r.rlim_cur = ((rlim_t) mem_limit) << 20;

#ifdef RLIMIT_AS

			setrlimit(RLIMIT_AS, &r); /* Ignore errors */

#else

			/* This takes care of OpenBSD, which doesn't have RLIMIT_AS, but
			 according to reliable sources, RLIMIT_DATA covers anonymous
			 maps - so we should be getting good protection against OOM bugs. */

			setrlimit(RLIMIT_DATA,&r); /* Ignore errors */

#endif /* ^RLIMIT_AS */

		}

		/* Dumping cores is slow and can lead to anomalies if SIGKILL is delivered
		 before the dump is complete. */

		r.rlim_max = r.rlim_cur = 0;

		setrlimit(RLIMIT_CORE,&r); /* Ignore errors */

		/* Isolate the process and configure standard descriptors. If out_file is
		 specified, stdin is /dev/null; otherwise, out_fd is cloned instead. */

		setsid();

		dup2(dev_null_fd,1);
		dup2(dev_null_fd,2);

		if (out_file || N_valid == 1)
		{ /* no stdin for file or network input */

			dup2(dev_null_fd,0);

		}
		else
		{

			dup2(out_fd,0);
			close(out_fd);

		}

		/* Set up control and status pipes, close the unneeded original fds. */

		if (dup2(ctl_pipe [ 0 ],FORKSRV_FD) < 0)
			PFATAL("dup2() failed");
		if (dup2(st_pipe [ 1 ],FORKSRV_FD + 1) < 0)
			PFATAL("dup2() failed");

		close(ctl_pipe [ 0 ]);
		close(ctl_pipe [ 1 ]);
		close(st_pipe [ 0 ]);
		close(st_pipe [ 1 ]);

		close(out_dir_fd);
		close(dev_null_fd);
		close(dev_urandom_fd);
		close(fileno(plot_file));

		/* This should improve performance a bit, since it stops the linker from
		 doing extra work post-fork(). */

		if (!getenv("LD_BIND_LAZY"))
			setenv("LD_BIND_NOW","1",0);

		/* Set sane defaults for ASAN if nothing else specified. */

		setenv("ASAN_OPTIONS","abort_on_error=1:"
				"detect_leaks=0:"
				"allocator_may_return_null=1",0);

		/* MSAN is tricky, because it doesn't support abort_on_error=1 at this
		 point. So, we do this in a very hacky way. */

		setenv("MSAN_OPTIONS","exit_code=" STRINGIFY(MSAN_ERROR) ":"
		"msan_track_origins=0",0);
		//argv是执行的参数
		execv(target_path,argv); //子进程启动qemu.execv会继承打开的文件描述符

		/* Use a distinctive bitmap signature to tell the parent about execv()
		 falling through. */

		*(u32*) trace_bits = EXEC_FAIL_SIG; //结束信号??
		exit(0);

	}

	/* Close the unneeded endpoints. */
	//parent process
	close(ctl_pipe [ 0 ]);
	close(st_pipe [ 1 ]);

	fsrv_ctl_fd = ctl_pipe [ 1 ]; //写管道
	fsrv_st_fd = st_pipe [ 0 ];  //读管道

	/* Wait for the fork server to come up, but don't wait too long. */

	it.it_value.tv_sec = ((exec_tmout * FORK_WAIT_MULT) / 1000);
	it.it_value.tv_usec = ((exec_tmout * FORK_WAIT_MULT) % 1000) * 1000;

	setitimer(ITIMER_REAL,&it,NULL);

	rlen = read(fsrv_st_fd,&status,4);  //从fsrv_st_fd管道读取4个字节的内容, 这里没有成功, 是为什么

	it.it_value.tv_sec = 0;
	it.it_value.tv_usec = 0;

	setitimer(ITIMER_REAL,&it,NULL);

	/* If we have a four-byte "hello" message from the server, we're all set.
	 Otherwise, try to figure out what went wrong. */

	if (rlen == 4)
	{
		OKF("All right - fork server is up.");
		return;
	}

	if (child_timed_out)
		FATAL("Timeout while initializing fork server (adjusting -t may help)");

	if (waitpid(forksrv_pid,&status,0) <= 0) //等待子进程结束
		PFATAL("waitpid() failed");

	if (WIFSIGNALED(status))
	{

		if (mem_limit && mem_limit < 500 && uses_asan)
		{

			SAYF(
					"\n" cLRD "[-] " cRST "Whoops, the target binary crashed suddenly, before receiving any input\n" "    from the fuzzer! Since it seems to be built with ASAN and you have a\n" "    restrictive memory limit configured, this is expected; please read\n" "    %s/notes_for_asan.txt for help.\n",
					doc_path);

		}
		else if (!mem_limit)
		{

			SAYF(
					"\n" cLRD "[-] " cRST "Whoops, the target binary crashed suddenly, before receiving any input\n" "    from the fuzzer! There are several probable explanations:\n\n"

					"    - The binary is just buggy and explodes entirely on its own. If so, you\n" "      need to fix the underlying problem or find a better replacement.\n\n"

#ifdef __APPLE__

					"    - On MacOS X, the semantics of fork() syscalls are non-standard and may\n"
					"      break afl-fuzz performance optimizations when running platform-specific\n"
					"      targets. To fix this, set AFL_NO_FORKSRV=1 in the environment.\n\n"

#endif /* __APPLE__ */

					"    - Less likely, there is a horrible bug in the fuzzer. If other options\n" "      fail, poke <lcamtuf@coredump.cx> for troubleshooting tips.\n");

		}
		else
		{

			SAYF(
					"\n" cLRD "[-] " cRST "Whoops, the target binary crashed suddenly, before receiving any input\n" "    from the fuzzer! There are several probable explanations:\n\n"

					"    - The current memory limit (%s) is too restrictive, causing the\n" "      target to hit an OOM condition in the dynamic linker. Try bumping up\n" "      the limit with the -m setting in the command line. A simple way confirm\n" "      this diagnosis would be:\n\n"

#ifdef RLIMIT_AS
					"      ( ulimit -Sv $[%llu << 10]; /path/to/fuzzed_app )\n\n"
#else
					"      ( ulimit -Sd $[%llu << 10]; /path/to/fuzzed_app )\n\n"
#endif /* ^RLIMIT_AS */

					"      Tip: you can use http://jwilk.net/software/recidivm to quickly\n" "      estimate the required amount of virtual memory for the binary.\n\n"

					"    - The binary is just buggy and explodes entirely on its own. If so, you\n" "      need to fix the underlying problem or find a better replacement.\n\n"

#ifdef __APPLE__

					"    - On MacOS X, the semantics of fork() syscalls are non-standard and may\n"
					"      break afl-fuzz performance optimizations when running platform-specific\n"
					"      targets. To fix this, set AFL_NO_FORKSRV=1 in the environment.\n\n"

#endif /* __APPLE__ */

					"    - Less likely, there is a horrible bug in the fuzzer. If other options\n" "      fail, poke <lcamtuf@coredump.cx> for troubleshooting tips.\n",
					DMS(mem_limit << 20),mem_limit - 1);

		}

		FATAL("Fork server crashed with signal %d",WTERMSIG(status));

	}

	if (*(u32*) trace_bits == EXEC_FAIL_SIG)
		FATAL("Unable to execute target application ('%s')",argv [ 0 ]);

	if (mem_limit && mem_limit < 500 && uses_asan)
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Hmm, looks like the target binary terminated before we could complete a\n" "    handshake with the injected code. Since it seems to be built with ASAN and\n" "    you have a restrictive memory limit configured, this is expected; please\n" "    read %s/notes_for_asan.txt for help.\n",
				doc_path);

	}
	else if (!mem_limit)
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Hmm, looks like the target binary terminated before we could complete a\n" "    handshake with the injected code. Perhaps there is a horrible bug in the\n" "    fuzzer. Poke <lcamtuf@coredump.cx> for troubleshooting tips.\n");

	}
	else
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Hmm, looks like the target binary terminated before we could complete a\n" "    handshake with the injected code. There are %s probable explanations:\n\n"

				"%s" "    - The current memory limit (%s) is too restrictive, causing an OOM\n" "      fault in the dynamic linker. This can be fixed with the -m option. A\n" "      simple way to confirm the diagnosis may be:\n\n"

#ifdef RLIMIT_AS
				"      ( ulimit -Sv $[%llu << 10]; /path/to/fuzzed_app )\n\n"
#else
				"      ( ulimit -Sd $[%llu << 10]; /path/to/fuzzed_app )\n\n"
#endif /* ^RLIMIT_AS */

				"      Tip: you can use http://jwilk.net/software/recidivm to quickly\n" "      estimate the required amount of virtual memory for the binary.\n\n"

				"    - Less likely, there is a horrible bug in the fuzzer. If other options\n" "      fail, poke <lcamtuf@coredump.cx> for troubleshooting tips.\n",
				getenv(DEFER_ENV_VAR) ? "three" : "two",
				getenv(DEFER_ENV_VAR) ? "    - You are using deferred forkserver, but __AFL_INIT() is never\n" "      reached before the program terminates.\n\n" : "",
				DMS(mem_limit << 20),mem_limit - 1);

	}

	FATAL("Fork server handshake failed");

}

/* Execute target application, monitoring for timeouts. Return status
 information. The called program will update trace_bits[]. */

static u8 run_target(char** argv)
{

	static struct itimerval it;
	static u32 prev_timed_out = 0;

	int status = 0;
	u32 tb4;

	child_timed_out = 0;

	/* check to ensure that network listener has executed if doing network
	 * fuzzing of a client target (where the target writes to a socket first */
	if (N_fuzz_client && !N_myaddr_valid)
	{
		network_setup_listener();
	}

	/* After this memset, trace_bits[] are effectively volatile, so we
	 must prevent any earlier operations from venturing into that
	 territory. */

	memset(trace_bits,0,MAP_SIZE);//每次都把trace_bits赋值为0.
	MEM_BARRIER();

	/* If we're running in "dumb" mode, we can't rely on the fork server
	 logic compiled into the target program, so we will just keep calling
	 execve(). There is a bit of code duplication between here and
	 init_forkserver(), but c'est la vie. */

	if (dumb_mode == 1 || no_forkserver)
	{

		child_pid = fork(); //自己fork,不利用qemu

		if (child_pid < 0)
			PFATAL("fork() failed");

		if (!child_pid)
		{ //子进程

			struct rlimit r;

			if (mem_limit)
			{

				r.rlim_max = r.rlim_cur = ((rlim_t) mem_limit) << 20;

#ifdef RLIMIT_AS

				setrlimit(RLIMIT_AS, &r); /* Ignore errors */

#else

				setrlimit(RLIMIT_DATA,&r); /* Ignore errors */

#endif /* ^RLIMIT_AS */

			}

			r.rlim_max = r.rlim_cur = 0;

			setrlimit(RLIMIT_CORE,&r); /* Ignore errors */

			/* Isolate the process and configure standard descriptors. If out_file is
			 specified, stdin is /dev/null; otherwise, out_fd is cloned instead. */

			setsid();

			dup2(dev_null_fd,1);
			dup2(dev_null_fd,2);

			if (out_file || N_valid == 1)
			{ /* no stdin for file or network input */

				dup2(dev_null_fd,0);

			}
			else
			{

				dup2(out_fd,0);
				close(out_fd);

			}

			/* On Linux, would be faster to use O_CLOEXEC. Maybe TODO. */

			close(dev_null_fd);
			close(out_dir_fd);
			close(dev_urandom_fd);
			close(fileno(plot_file));

			/* Set sane defaults for ASAN if nothing else specified. */

			setenv("ASAN_OPTIONS","abort_on_error=1:"
					"detect_leaks=0:"
					"allocator_may_return_null=1",0);

			setenv("MSAN_OPTIONS","exit_code=" STRINGIFY(MSAN_ERROR) ":"
			"msan_track_origins=0",0);

			execv(target_path,argv);

			/* Use a distinctive bitmap value to tell the parent about execv()
			 falling through. */

			*(u32*) trace_bits = EXEC_FAIL_SIG;
			exit(0);

		}

	}
	else
	{ //可以fork,或者有forkserver,默认是可以的

		s32 res;

		/* In non-dumb mode, we have the fork server up and running, so simply
		 tell it to have at it, and then read back PID. */

		if ((res = write(fsrv_ctl_fd,&prev_timed_out,4)) != 4)
		{ //告诉 qemu 可以开始测试

			if (stop_soon)
				return 0;
			RPFATAL(res,
					"Unable to request new process from fork server (OOM?)");

		}

		if ((res = read(fsrv_st_fd,&child_pid,4)) != 4)
		{ //控制管道  读取的测试进程的pid

			if (stop_soon)
				return 0;
			RPFATAL(res,
					"Unable to request new process from fork server (OOM?)");

		}

		if (child_pid <= 0)
			FATAL("Fork server is misbehaving (OOM?)");

	}

	/* Write fuzzed data set to target using network if -N option is specified */

	if (N_valid)
	{
		if (N_timeout_given)
		{
			/* Network output to target process after specified delay, and try
			 * up to three times (hard-coded) */
			N_it.tv_sec = (N_exec_tmout / 1000);
			N_it.tv_nsec = (N_exec_tmout % 1000) * 1000000;
			/* ignore errors & accept possibility that delay can be shorter */
			{
				u32 N_tries = 3;
				nanosleep(&N_it,NULL);
				/* attempt to send up to 3 times (because of target process startup time) */
				while (N_tries--
						&& ((N_fuzz_client ? network_listen() : network_send())
								== -1))
					;
			}
		}
		else
		{
			/* Network output to target process - no delay.  This usual won't work. */
			if ((N_fuzz_client ? network_listen() : network_send()) == -1)
			{
				FATAL(
						"Network: failed to connect or send; specify a network delay time");
			}
		}
	}

	/* Configure timeout, as requested by user, then wait for child to terminate. */

	it.it_value.tv_sec = (exec_tmout / 1000);
	it.it_value.tv_usec = (exec_tmout % 1000) * 1000;

	setitimer(ITIMER_REAL,&it,NULL); //设置超时设置,启动定时器

	/* The SIGALRM handler simply kills the child_pid and sets child_timed_out. */ //注册了handle_timeout函数

	if (dumb_mode == 1 || no_forkserver)
	{

		if (waitpid(child_pid,&status,0) <= 0)
			PFATAL("waitpid() failed");

	}
	else
	{

		s32 res;

		if ((res = read(fsrv_st_fd,&status,4)) != 4)
		{ //从qemu中读取状态信息

			if (stop_soon)
				return 0;
			RPFATAL(res,"Unable to communicate with fork server");

		}

	}

	child_pid = 0;
	it.it_value.tv_sec = 0;
	it.it_value.tv_usec = 0;

	setitimer(ITIMER_REAL,&it,NULL); //清除定时器

	total_execs++; //execve函数的调用次数 ,这个也是记录的测试用例的次数

	/* Any subsequent operations on trace_bits must not be moved by the
	 compiler below this point. Past this location, trace_bits[] behave
	 very normally and do not have to be treated as volatile. */

	MEM_BARRIER();
	//再次内存屏障,保证trace_bit的值都配置好了

	tb4 = *(u32*) trace_bits;

#ifdef __x86_64__
	classify_counts((u64*)trace_bits); //对tracer_bit进行记录操作,归一到滚筒关系
#else
	classify_counts((u32*) trace_bits); //对tracer_bit进行记录操作,归一到滚筒关系
#endif /* ^__x86_64__ */

	prev_timed_out = child_timed_out;



	/* Report outcome to caller. */

	if (child_timed_out)  //判断子进程是否超时
		return FAULT_HANG; //时间太长,挂起

	if (WIFSIGNALED(status) && !stop_soon)
	{ //判断测试进程是否异常退出,即由信号中止 这里所有信号都是crash吗
		kill_signal = WTERMSIG(status); //得知中止进程的信号值,和kill -l是对应的
		return FAULT_CRASH;
	}

	/* A somewhat nasty hack for MSAN, which doesn't support abort_on_error and
	 must use a special exit code. */

	if (uses_asan && WEXITSTATUS(status) == MSAN_ERROR)
	{
		kill_signal = 0;
		return FAULT_CRASH;
	}

	if ((dumb_mode == 1 || no_forkserver) && tb4 == EXEC_FAIL_SIG)
		return FAULT_ERROR;

	return FAULT_NONE;

}

/* Write modified data to file for testing. If out_file is set, the old file
 is unlinked and a new one is created. Otherwise, out_fd is rewound and
 truncated. */

static void write_to_testcase(void* mem, u32 len)
{ //将变异后的测试用例写入到 /output/.cur_input中

	s32 fd = out_fd;

	if (out_file)
	{

		unlink(out_file); /* Ignore errors. */

		fd = open(out_file,O_WRONLY | O_CREAT | O_EXCL,0600);

		if (fd < 0)
			PFATAL("Unable to create '%s'",out_file);

	}
	else
		lseek(fd,0,SEEK_SET);

	ck_write(fd,mem,len,out_file); //将mem的内容写入到fd中,即/output/.cur_input下

	if (!out_file)
	{

		if (ftruncate(fd,len))
			PFATAL("ftruncate() failed");
		lseek(fd,0,SEEK_SET);

	}
	else
		close(fd);

}

/* The same, but with an adjustable gap. Used for trimming. */

static void write_with_gap(void* mem, u32 len, u32 skip_at, u32 skip_len)
{

	s32 fd = out_fd;
	u32 tail_len = len - skip_at - skip_len; //末尾保留的,可能为0.

	if (out_file)
	{

		unlink(out_file); /* Ignore errors. */

		fd = open(out_file,O_WRONLY | O_CREAT | O_EXCL,0600);

		if (fd < 0)
			PFATAL("Unable to create '%s'",out_file);

	}
	else
		lseek(fd,0,SEEK_SET);

	if (skip_at)
		ck_write(fd,mem,skip_at,out_file); //skip_at是长度  写入到.cur_input中 保留的位数

	if (tail_len)
		ck_write(fd,mem + skip_at + skip_len,tail_len,out_file); //跳过了skip_len长度的字节

	if (!out_file)
	{

		if (ftruncate(fd,len - skip_len))
			PFATAL("ftruncate() failed");
		lseek(fd,0,SEEK_SET);

	}
	else
		close(fd);

}

static void show_stats(void);

/* Calibrate a new test case. This is done when processing the input directory
 to warn about flaky or otherwise problematic test cases early on; and when
 new paths are discovered to detect variable behavior and so on. */

static u8 calibrate_case(char** argv, struct queue_entry* q, u8* use_mem,
		u32 handicap, u8 from_queue)
{

	u8 fault = 0 , new_bits = 0 , var_detected = 0 , first_run = (q->exec_cksum
			== 0);
	u64 start_us , stop_us;

	s32 old_sc = stage_cur , old_sm = stage_max , old_tmout = exec_tmout;
	u8* old_sn = stage_name;

	/* Be a bit more generous about timeouts when resuming sessions, or when
	 trying to calibrate already-added finds. This helps avoid trouble due
	 to intermittent latency. */

	if (!from_queue || resuming_fuzz)
		exec_tmout = MAX(exec_tmout + CAL_TMOUT_ADD,
				exec_tmout * CAL_TMOUT_PERC / 100);

	q->cal_failed++;

	stage_name = "calibration";
	stage_max = no_var_check ? CAL_CYCLES_NO_VAR : CAL_CYCLES; //循环次数 多次calibration的意义

	/* Make sure the forkserver is up before we do anything, and let's not
	 count its spin-up time toward binary calibration. */

	if (dumb_mode != 1 && !no_forkserver && !forksrv_pid)
		init_forkserver(argv); //setup forkserver  一种argv是启动qemu的参数 这里启动qemu

	start_us = get_cur_time_us();

	for (stage_cur = 0; stage_cur < stage_max; stage_cur++)
	{

		u32 cksum;

		if (!first_run && !(stage_cur % stats_update_freq))
			show_stats();

		write_to_testcase(use_mem,q->len); //将测试用例的值保存到/output/.cur_input下

		fault = run_target(argv); //argv指向目标程序

		/* stop_soon is set by the handler for Ctrl+C. When it's pressed,
		 we want to bail out quickly. */

		if (stop_soon || fault != crash_mode)
			goto abort_calibration;

		if (!dumb_mode && !stage_cur && !count_bytes(trace_bits))
		{
			fault = FAULT_NOINST; //没有命中基本块
			goto abort_calibration;
			//该测试用例不行? 还有时间限制,调试的时候容易hang住
		}

		cksum = hash32(trace_bits,MAP_SIZE,HASH_CONST);  //求哈希值

		if (q->exec_cksum != cksum)
		{ //判断是否是新的轨迹 只在calibration过程中

			u8 hnb = has_new_bits(virgin_bits); //函数里调用了trace_bits hnb=2表示运行到新的基本块了
			if (hnb > new_bits)
				new_bits = hnb;

			if (!no_var_check && q->exec_cksum)
			{

				var_detected = 1; //表示同一个测试用例,不同次测试,路径不一致,即有随机路径
				stage_max = CAL_CYCLES_LONG; //CAL_CYCLES_LONGshi 40

			}
			else
				q->exec_cksum = cksum; //该测试用例第一次测试

		}

	}

	stop_us = get_cur_time_us();

	total_cal_us += stop_us - start_us;
	total_cal_cycles += stage_max;

	/* OK, let's collect some stats about the performance of this test case.
	 This is used for fuzzing air time calculations in calculate_score(). */

	q->exec_us = (stop_us - start_us) / stage_max;
	q->bitmap_size = count_bytes(trace_bits); //统计有多少个元组关系
	q->handicap = handicap; //表示是第几次大循环中生成的
	q->cal_failed = 0;

	total_bitmap_size += q->bitmap_size; // 总的元组关系,有重复
	total_bitmap_entries++;

	update_bitmap_score(q); //对测试用例打分, 如果测试用例不好,就不加入到top_rated[ ]数组中

	/* If this case didn't result in new output from the instrumentation, tell
	 parent. This is a non-critical problem, but something to warn the user
	 about. */

	if (!dumb_mode && first_run && !fault && !new_bits)
		fault = FAULT_NOBITS;

	abort_calibration:

	if (new_bits == 2 && !q->has_new_cov)
	{
		q->has_new_cov = 1;
		queued_with_cov++;
	}

	/* Mark variable paths. */

	if (var_detected && !q->var_behavior)
	{
		mark_as_variable(q);
		queued_variable++;
	}

	stage_name = old_sn;  //恢复原来的配置
	stage_cur = old_sc;
	stage_max = old_sm;
	exec_tmout = old_tmout;

	if (!first_run)
		show_stats();

	return fault;

}

/* Examine map coverage. Called once, for first test case. */

static void check_map_coverage(void)
{

	u32 i;

	if (count_bytes(trace_bits) < 100)
		return; //基本块数量小于100 ,就返回?

	for (i = (1 << (MAP_SIZE_POW2 - 1)); i < MAP_SIZE; i++) //从2^15 到2^16
		if (trace_bits [ i ])
			return;

	WARNF("Recompile binary with newer version of afl to improve coverage!");

}

/* Perform dry run of all test cases to confirm that the app is working as
 expected. This is done only for the initial inputs, and only once. */

static void perform_dry_run(char** argv)
{ //这个是参数集合

	struct queue_entry* q = queue;
	u32 cal_failures = 0;
	u8* skip_crashes = getenv("AFL_SKIP_CRASHES");

	while (q)
	{

		u8* use_mem; //testcase的内容
		u8 res;
		s32 fd;

		u8* fn = strrchr(q->fname,'/') + 1; //strchr,最后一次出现的位置,即指向最后的文件名

		ACTF("Attempting dry run with '%s'...",fn);

		fd = open(q->fname,O_RDONLY); //成功返回文件描述符
		if (fd < 0)
			PFATAL("Unable to open '%s'",q->fname);

		use_mem = ck_alloc_nozero(q->len);

		if (read(fd,use_mem,q->len) != q->len)
			FATAL("Short read from '%s'",q->fname);

		close(fd);
		///完成testcase 内容复制
		res = calibrate_case(argv,q,use_mem,0,1); //测试用例的可用性测试 返回运行结果
		ck_free(use_mem);

		if (stop_soon)
			return;

		if (res == crash_mode || res == FAULT_NOBITS) //??
			SAYF(
					cGRA "    len = %u, map size = %u, exec speed = %llu us\n" cRST,
					q->len,q->bitmap_size,q->exec_us); //用于显示

		switch (res)
		{

			case FAULT_NONE :

				if (q == queue)
					check_map_coverage(); //这个函数奇怪,先不管.

				if (crash_mode)
					FATAL("Test case '%s' does *NOT* crash",fn); //fatal 退出了

				break;

			case FAULT_HANG :

				if (timeout_given)
				{

					/* The -t nn+ syntax in the command line sets timeout_given to '2' and
					 instructs afl-fuzz to tolerate but skip queue entries that time
					 out. */

					if (timeout_given > 1)
					{
						WARNF("Test case results in a hang (skipping)");
						q->cal_failed = CAL_CHANCES;
						cal_failures++;
						break;
					}

					SAYF(
							"\n" cLRD "[-] " cRST "The program took more than %u ms to process one of the initial test cases.\n" "    Usually, the right thing to do is to relax the -t option - or to delete it\n" "    altogether and allow the fuzzer to auto-calibrate. That said, if you know\n" "    what you are doing and want to simply skip the unruly test cases, append\n" "    '+' at the end of the value passed to -t ('-t %u+').\n",
							exec_tmout,exec_tmout);

					FATAL("Test case '%s' results in a hang",fn);

				}
				else
				{

					SAYF(
							"\n" cLRD "[-] " cRST "The program took more than %u ms to process one of the initial test cases.\n" "    This is bad news; raising the limit with the -t option is possible, but\n" "    will probably make the fuzzing process extremely slow.\n\n"

							"    If this test case is just a fluke, the other option is to just avoid it\n" "    altogether, and find one that is less of a CPU hog.\n",
							exec_tmout);

					FATAL("Test case '%s' results in a hang",fn);

				}

			case FAULT_CRASH :

				if (crash_mode)
					break;

				if (skip_crashes)
				{
					WARNF("Test case results in a crash (skipping)");
					q->cal_failed = CAL_CHANCES;
					cal_failures++;
					break;
				}

				if (mem_limit)
				{

					SAYF(
							"\n" cLRD "[-] " cRST "Oops, the program crashed with one of the test cases provided. There are\n" "    several possible explanations:\n\n"

							"    - The test case causes known crashes under normal working conditions. If\n" "      so, please remove it. The fuzzer should be seeded with interesting\n" "      inputs - but not ones that cause an outright crash.\n\n"

							"    - The current memory limit (%s) is too low for this program, causing\n" "      it to die due to OOM when parsing valid files. To fix this, try\n" "      bumping it up with the -m setting in the command line. If in doubt,\n" "      try something along the lines of:\n\n"

#ifdef RLIMIT_AS
							"      ( ulimit -Sv $[%llu << 10]; /path/to/binary [...] <testcase )\n\n"
#else
							"      ( ulimit -Sd $[%llu << 10]; /path/to/binary [...] <testcase )\n\n"
#endif /* ^RLIMIT_AS */

							"      Tip: you can use http://jwilk.net/software/recidivm to quickly\n" "      estimate the required amount of virtual memory for the binary. Also,\n" "      if you are using ASAN, see %s/notes_for_asan.txt.\n\n"

#ifdef __APPLE__

							"    - On MacOS X, the semantics of fork() syscalls are non-standard and may\n"
							"      break afl-fuzz performance optimizations when running platform-specific\n"
							"      binaries. To fix this, set AFL_NO_FORKSRV=1 in the environment.\n\n"

#endif /* __APPLE__ */

							"    - Least likely, there is a horrible bug in the fuzzer. If other options\n" "      fail, poke <lcamtuf@coredump.cx> for troubleshooting tips.\n",
							DMS(mem_limit << 20),mem_limit - 1,doc_path);

				}
				else
				{

					SAYF(
							"\n" cLRD "[-] " cRST "Oops, the program crashed with one of the test cases provided. There are\n" "    several possible explanations:\n\n"

							"    - The test case causes known crashes under normal working conditions. If\n" "      so, please remove it. The fuzzer should be seeded with interesting\n" "      inputs - but not ones that cause an outright crash.\n\n"

#ifdef __APPLE__

							"    - On MacOS X, the semantics of fork() syscalls are non-standard and may\n"
							"      break afl-fuzz performance optimizations when running platform-specific\n"
							"      binaries. To fix this, set AFL_NO_FORKSRV=1 in the environment.\n\n"

#endif /* __APPLE__ */

							"    - Least likely, there is a horrible bug in the fuzzer. If other options\n" "      fail, poke <lcamtuf@coredump.cx> for troubleshooting tips.\n");

				}

				FATAL("Test case '%s' results in a crash",fn);

			case FAULT_ERROR :

				FATAL("Unable to execute target application ('%s')",argv [ 0 ]);

			case FAULT_NOINST :

				FATAL("No instrumentation detected");

			case FAULT_NOBITS :

				useless_at_start++;

				if (!in_bitmap)
					WARNF(
							"No new instrumentation output, test case may be useless.");

				break;

		}

		if (q->var_behavior)
			WARNF("Instrumentation output varies across runs.");

		q = q->next;

	}

	if (cal_failures)
	{

		if (cal_failures == queued_paths)
			FATAL("All test cases time out%s, giving up!",
					skip_crashes ? " or crash" : "");

		WARNF("Skipped %u test cases (%0.02f%%) due to timeouts%s.",
				cal_failures,((double )cal_failures) * 100 / queued_paths,
				skip_crashes ? " or crashes" : "");

		if (cal_failures * 5 > queued_paths)
			WARNF(
					cLRD "High percentage of rejected test cases, check settings!");

	}

	OKF("All test cases processed.");

}

/* Helper function: link() if possible, copy otherwise. */

static void link_or_copy(u8* old_path, u8* new_path)
{

	s32 i = link(old_path,new_path);
	s32 sfd , dfd;
	u8* tmp;

	if (!i)
		return;

	sfd = open(old_path,O_RDONLY);
	if (sfd < 0)
		PFATAL("Unable to open '%s'",old_path);

	dfd = open(new_path,O_WRONLY | O_CREAT | O_EXCL,0600);
	if (dfd < 0)
		PFATAL("Unable to create '%s'",new_path);

	tmp = ck_alloc(64 * 1024);

	while ((i = read(sfd,tmp,64 * 1024)) > 0)
		ck_write(dfd,tmp,i,new_path);

	if (i < 0)
		PFATAL("read() failed");

	ck_free(tmp);
	close(sfd);
	close(dfd);

}

static void nuke_resume_dir(void);

/* Create hard links for input test cases in the output directory, choosing
 good names and pivoting accordingly. */

static void pivot_inputs(void)
{

	struct queue_entry* q = queue;
	u32 id = 0;

	ACTF("Creating hard links for all input files...");

	while (q)
	{

		u8 *nfn , *rsl = strrchr(q->fname,'/');
		u32 orig_id;

		if (!rsl)
			rsl = q->fname;
		else
			rsl++;

		/* If the original file name conforms to the syntax and the recorded
		 ID matches the one we'd assign, just use the original file name.
		 This is valuable for resuming fuzzing runs. */

#ifndef SIMPLE_FILES
#  define CASE_PREFIX "id:"
#else
#  define CASE_PREFIX "id_"
#endif /* ^!SIMPLE_FILES */

		if (!strncmp(rsl,CASE_PREFIX,3) && sscanf(rsl + 3,"%06u",&orig_id) == 1
				&& orig_id == id)
		{

			u8* src_str;
			u32 src_id;

			resuming_fuzz = 1;
			nfn = alloc_printf("%s/queue/%s",out_dir,rsl);

			/* Since we're at it, let's also try to find parent and figure out the
			 appropriate depth for this entry. */

			src_str = strchr(rsl + 3,':');

			if (src_str && sscanf(src_str + 1,"%06u",&src_id) == 1)
			{

				struct queue_entry* s = queue;
				while (src_id-- && s)
					s = s->next;
				if (s)
					q->depth = s->depth + 1;

				if (max_depth < q->depth)
					max_depth = q->depth;

			}

		}
		else
		{

			/* No dice - invent a new name, capturing the original one as a
			 substring. */

#ifndef SIMPLE_FILES

			u8* use_name = strstr(rsl,",orig:");

			if (use_name)
				use_name += 6;
			else
				use_name = rsl;
			nfn = alloc_printf("%s/queue/id:%06u,orig:%s",out_dir,id,use_name);

#else

			nfn = alloc_printf("%s/queue/id_%06u", out_dir, id);

#endif /* ^!SIMPLE_FILES */

		}

		/* Pivot to the new queue entry. */

		link_or_copy(q->fname,nfn); //将初始测试用例赋值到output/queue下
		ck_free(q->fname);
		q->fname = nfn;  //queue队列指向 /output/queue下

		/* Make sure that the passed_det value carries over, too. */

		if (q->passed_det)
			mark_as_det_done(q);

		q = q->next;
		id++;

	}

	if (in_place_resume)
		nuke_resume_dir();

}

#ifndef SIMPLE_FILES

/* Construct a file name for a new test case, capturing the operation
 that led to its discovery. Uses a static buffer. */

static u8* describe_op(u8 hnb)
{ //这个函数记录了测试用例的操作

	static u8 ret [ 256 ];

	if (syncing_party)
	{

		sprintf(ret,"sync:%s,src:%06u",syncing_party,syncing_case);

	}
	else
	{

		sprintf(ret,"src:%06u",current_entry); //变异来源

		if (splicing_with >= 0)
			sprintf(ret + strlen(ret),"+%06u",splicing_with);

		sprintf(ret + strlen(ret),",op:%s",stage_short);

		if (stage_cur_byte >= 0)
		{

			sprintf(ret + strlen(ret),",pos:%u",stage_cur_byte);

			if (stage_val_type != STAGE_VAL_NONE)
				sprintf(ret + strlen(ret),",val:%s%+d",
						(stage_val_type == STAGE_VAL_BE) ? "be:" : "",
						stage_cur_val); //stage_cur_val表示计算过程中加减的值,有正负

		}
		else
			sprintf(ret + strlen(ret),",rep:%u",stage_cur_val); //havoc阶段的循环次数

	}

	if (hnb == 2)
		strcat(ret,",+cov"); //全新的元组关系,不包括滚筒的升级

	return ret;

}

#endif /* !SIMPLE_FILES */

/* Write a message accompanying the crash directory :-) */

static void write_crash_readme(void)
{

	u8* fn = alloc_printf("%s/crashes/README.txt",out_dir);
	s32 fd;
	FILE* f;

	fd = open(fn,O_WRONLY | O_CREAT | O_EXCL,0600);
	ck_free(fn);

	/* Do not die on errors here - that would be impolite. */

	if (fd < 0)
		return;

	f = fdopen(fd,"w");

	if (!f)
	{
		close(fd);
		return;
	}

	fprintf(f,
			"Command line used to find this crash:\n\n"

					"%s\n\n"

					"If you can't reproduce a bug outside of afl-fuzz, be sure to set the same\n"
					"memory limit. The limit used for this fuzzing session was %s.\n\n"

					"Need a tool to minimize test cases before investigating the crashes or sending\n"
					"them to a vendor? Check out the afl-tmin that comes with the fuzzer!\n\n"

					"Found any cool bugs in open-source tools using afl-fuzz? If yes, please drop\n"
					"me a mail at <lcamtuf@coredump.cx> once the issues are fixed - I'd love to\n"
					"add your finds to the gallery at:\n\n"

					"  http://lcamtuf.coredump.cx/afl/\n\n"

					"Thanks :-)\n",

			orig_cmdline,DMS(mem_limit << 20)); /* ignore errors */

	fclose(f);

}

/* Check if the result of an execve() during routine fuzzing is interesting,
 save or queue the input test case for further analysis if so. Returns 1 if
 entry is saved, 0 otherwise. */

static u8 save_if_interesting(char** argv, void* mem, u32 len, u8 fault)
{

	u8 *fn = "";

#ifdef XIAOSA
	u8* tmpy = "";
	s32 fdy;

	//for cycle
	u32 i = 0;
	u32 j = 0;

	//for the len of the string
	s32 ylen;
#endif

	u8 hnb;
	s32 fd;
	u8 keeping = 0 , res;

	if (fault == crash_mode)
	{//根据模式决定记录哪些测试用例
	 //如果crash_mode=0,这里不会收集crash的执行轨迹

		/* Keep only if there are new bits in the map, add to queue for
		 future fuzzing, etc. */
		if (!(hnb = has_new_bits(virgin_bits))) //这里根据有滚筒策略的trace_bit比较.
		{ //没有新的元组关系被执行
			if (crash_mode)
				total_crashes++;
			return 0;
		}

#ifndef SIMPLE_FILES
		//发现新的元组关系
		fn = alloc_printf("%s/queue/id:%06u,%s",out_dir,queued_paths,
				describe_op(hnb));
#else
		fn = alloc_printf("%s/queue/id_%06u", out_dir, queued_paths);

#endif /* ^!SIMPLE_FILES */

		add_to_queue(fn,len,0); //添加到变量 ,配置了queue_top.crash的测试用例不用添加到这里,除非是crash模式
		if (hnb == 2)
		{
			queue_top->has_new_cov = 1;
			queued_with_cov++; //没有考虑滚筒的变换
		}
		queue_top->exec_cksum = hash32(trace_bits,MAP_SIZE,HASH_CONST);

		/* Try to calibrate inline; this also calls update_bitmap_score() when
		 successful. */
		res = calibrate_case(argv,queue_top,mem,queue_cycle - 1,0); //处理一下要新的测试用例
		if (res == FAULT_ERROR)
			FATAL("Unable to execute target application");
		fd = open(fn,O_WRONLY | O_CREAT | O_EXCL,0600);
		if (fd < 0)
			PFATAL("Unable to create '%s'",fn);
		ck_write(fd,mem,len,fn); //在queue目录下保存新的测试用例,这里并不会保存crash和hang
		close(fd);

//#if 0
#ifdef XIAOSA
		//保存新的测试用例的基本块地址跳跃信息
		//这一部分可以写到minimize_bits函数里

		//先保存总的信息,方便查看
		tmpy = alloc_printf("%s/queue_trace_mini/total",out_dir);
		fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND ,0600);
		if (fdy < 0)
			PFATAL("Unable to create '%s'",tmpy);
		ck_free(tmpy);

		tmpy =
				alloc_printf(
						"id:%06u %s is in the top_rate, block number is:%-6u,its parent is id:%06d\n",
						queued_paths - 1,queue_top->in_top_rate ? "   " : "not",
						queue_top->bitmap_size,current_entry);
		ylen = snprintf(NULL,0,"%s",tmpy);
		write(fdy,tmpy,ylen);
		ck_free(tmpy);
		close(fdy);

#if 1
		//保存每个测试用例的路径到一个单独文件
		tmpy = alloc_printf("%s/queue_trace_mini/%u",out_dir,queued_paths - 1); //前面add_to_queue使得queued_paths+1,这里-1保持id一致
		fdy = open(tmpy,O_WRONLY | O_CREAT | O_EXCL,0600);
		if (fdy < 0)
			PFATAL("Unable to create '%s'",tmpy);
		ck_free(tmpy);


		if (queue_top->trace_mini != 0) //这里为0,就是表示没有进入top_rate数组  xiaosa在update函数中修改了,所有的都记录
		{

			while (i < MAP_SIZE)
			{ //65536次循环,16位11
				if (queue_top->trace_mini [ i >> 3 ] & 1 << (i & 7))
				{	//即该基本被执行
					/*if ((j & 15) == 0 && (j != 0))
						write(fd,"\n",1);*/
					tmpy = alloc_printf("%-6u\n",i);
					ylen = snprintf(NULL,0,"%s",tmpy);
					write(fdy,tmpy,ylen);	//保存新的测试用例
					ck_free(tmpy);
					j++;
				}
				i++;
			}
		}
#endif
		close(fdy);

#endif


#ifdef XIAOSA
		//添加配置信息
		queue_cur->nm_child++; // child number add 1
		queue_top->change_op = alloc_printf("%s",describe_op(hnb));
		queue_top->parent_id = current_entry; //
		queue_top->self_id = queued_paths - 1; //

		//save some 测试用例变异的递进关系 information in the output catalog
		// generate the string of target file
		tmpy = alloc_printf("%s/test_add.plot",out_dir);
		fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
		if (fdy < 0)
			PFATAL("Unable to create '%s'",tmpy);
		ck_free(tmpy);

		//fn_xs = alloc_printf("	%d->%d[label=\"%s\"];\n",queue_top->parent_id,queue_top->self_id, queue_top->change_op);
		tmpy = alloc_printf("	%u->%u;\n",queue_cur->self_id,queue_top->self_id);
		ck_write(fdy,tmpy,strlen(tmpy),"test_add.plot");
		ck_free(tmpy);

		close(fdy);
#endif

		keeping = 1;
	}

	switch (fault)
	{

		case FAULT_HANG :

			/* Hangs are not very interesting, but we're still obliged to keep
			 a handful of samples. We use the presence of new bits in the
			 hang-specific bitmap as a signal of uniqueness. In "dumb" mode, we
			 just keep everything. */

			total_hangs++;

			if (unique_hangs >= KEEP_UNIQUE_HANG)
				return keeping;

			if (!dumb_mode)
			{

#ifdef __x86_64__
				simplify_trace((u64*)trace_bits);
#else
				simplify_trace((u32*) trace_bits);
#endif /* ^__x86_64__ */

				if (!has_new_bits(virgin_hang))
					return keeping;

			}

#ifndef SIMPLE_FILES

			fn = alloc_printf("%s/hangs/id:%06llu,%s",out_dir,unique_hangs,
					describe_op(0));

#else

			fn = alloc_printf("%s/hangs/id_%06llu", out_dir,
					unique_hangs);

#endif /* ^!SIMPLE_FILES */

			unique_hangs++;

			last_hang_time = get_cur_time();

			break;

		case FAULT_CRASH :

			/* This is handled in a manner roughly similar to hangs,
			 except for slightly different limits. */

			total_crashes++;

			if (unique_crashes >= KEEP_UNIQUE_CRASH)
				return keeping;

			if (!dumb_mode)
			{

#ifdef __x86_64__
				simplify_trace((u64*)trace_bits); //化简测试用例的执行轨迹,即滚筒值归一到1和128,1表示没有击中,128表示击中
#else
				simplify_trace((u32*) trace_bits);
#endif /* ^__x86_64__ */


				if (!has_new_bits(virgin_crash)) //当前测试用例的trace_bit和一个总的比较,判断是否是新的crash
					return keeping;

			}

			if (!unique_crashes)
				write_crash_readme();

#ifndef SIMPLE_FILES

			fn = alloc_printf("%s/crashes/id:%06llu,sig:%02u,%s",out_dir,
					unique_crashes,kill_signal,describe_op(0));

#else

			fn = alloc_printf("%s/crashes/id_%06llu_%02u", out_dir, unique_crashes,
					kill_signal);

#endif /* ^!SIMPLE_FILES */

			unique_crashes++;

			last_crash_time = get_cur_time();
//#if 0
#ifdef XIAOSA
			//save some 测试用例变异递进关系 information from crash catalog
			// generate the string of target file
			tmpy = alloc_printf("%s/test_add.plot",out_dir);
			fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
			if (fdy < 0)
				PFATAL("Unable to create '%s'",tmpy);
			ck_free(tmpy);

			// add the crash node
			tmpy = alloc_printf(
					"	crash%llu[style = filled,color=burlywood2];\n",
					unique_crashes-1);
			ck_write(fdy,tmpy,strlen(tmpy),"test_add.plot");
			ck_free(tmpy);

			//add the edge  o the crash testcase
			tmpy = alloc_printf("	%u->crash%llu[color=red];\n",
					queue_cur->self_id,unique_crashes-1);
			ck_write(fdy,tmpy,strlen(tmpy),"test_add.plot");
			ck_free(tmpy);

			close(fdy);
#endif

//#if 0
#ifdef XIAOSA
			//保存crash测试用例的基本块地址跳跃信息
			//这一部分可以写到minimize_bits函数里

			//先保存总的信息,方便查看 ,,这里还没有该!!!

#if 1
			//每个crash测试用例的执行轨迹信息保存到一个单独文件
			queue_cur->nm_crash_child++;
			tmpy = alloc_printf("%s/crash_trace_mini/crash:%llu",out_dir,
					unique_crashes - 1);
			fdy = open(tmpy,O_WRONLY | O_CREAT | O_EXCL,0600);
			if (fdy < 0)
				PFATAL("Unable to create '%s'",tmpy);
			ck_free(tmpy);

			////
			//这里可以改成64位操作
			i = 0 ; //65536次
			while (i++ < MAP_SIZE)
			{
				if (trace_bits [ i ] == 128)
				{
					//save the relation of the tuple
					tmpy = alloc_printf("%-6u\n",i);
					ylen = snprintf(NULL,0,"%s",tmpy);
					write(fdy,tmpy,ylen);	//保存新的测试用例
					ck_free(tmpy);
				}

			}
#endif
			close(fdy);

#if 0
			//save the execution number of the tuple that in crash testcase

			u8 * tmpy = "";
			tmpy = alloc_printf("%s/crash_trace_mini/%llu_executed_number",out_dir,
								unique_crashes - 1);
			remove(tmpy);
			fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600);
			if (fdy < 0)
				PFATAL("Unable to create '%s'",tmpy);
			ck_free(tmpy);

			for (i = 0; i < MAP_SIZE; i++)
			{
				if (trace_bits [ i ]== 128)
				{

					tmpy = alloc_printf("NO.%d is executed %-20u times;\n",i,
							virgin_counts [ i ]);
					ck_write(fdy,tmpy,strlen(tmpy),"each crash executed number");
					ck_free(tmpy);
				}

			}
			close(fdy);

#endif

#endif

			break;

		case FAULT_ERROR :
			FATAL("Unable to execute target application");

		default :
			return keeping;

	}

	/* If we're here, we apparently want to save the crash or hang
	 test case, too. */

	fd = open(fn,O_WRONLY | O_CREAT | O_EXCL,0600);
	if (fd < 0)
		PFATAL("Unable to create '%s'",fn);
	ck_write(fd,mem,len,fn);
	close(fd);
	ck_free(fn);

	return keeping; //1 表示有新的元组关系出现

}

/* When resuming, try to find the queue position to start from. This makes sense
 only when resuming, and when we can find the original fuzzer_stats. */

static u32 find_start_position(void)
{

	static u8 tmp [ 4096 ]; /* Ought to be enough for anybody. */

	u8 *fn , *off;
	s32 fd , i;
	u32 ret;

	if (!resuming_fuzz)
		return 0;

	if (in_place_resume)
		fn = alloc_printf("%s/fuzzer_stats",out_dir);
	else
		fn = alloc_printf("%s/../fuzzer_stats",in_dir);

	fd = open(fn,O_RDONLY);
	ck_free(fn);

	if (fd < 0)
		return 0;

	i = read(fd,tmp,sizeof(tmp) - 1);
	(void) i; /* Ignore errors */
	close(fd);

	off = strstr(tmp,"cur_path       : ");
	if (!off)
		return 0;

	ret = atoi(off + 17);
	if (ret >= queued_paths)
		ret = 0;
	return ret;

}

/* The same, but for timeouts. The idea is that when resuming sessions without
 -t given, we don't want to keep auto-scaling the timeout over and over
 again to prevent it from growing due to random flukes. */

static void find_timeout(void)
{

	static u8 tmp [ 4096 ]; /* Ought to be enough for anybody. */

	u8 *fn , *off;
	s32 fd , i;
	u32 ret;

	if (!resuming_fuzz)
		return;

	if (in_place_resume)
		fn = alloc_printf("%s/fuzzer_stats",out_dir);
	else
		fn = alloc_printf("%s/../fuzzer_stats",in_dir);

	fd = open(fn,O_RDONLY);
	ck_free(fn);

	if (fd < 0)
		return;

	i = read(fd,tmp,sizeof(tmp) - 1);
	(void) i; /* Ignore errors */
	close(fd);

	off = strstr(tmp,"exec_timeout   : ");
	if (!off)
		return;

	ret = atoi(off + 17);
	if (ret <= 4)
		return;

	exec_tmout = ret;
	timeout_given = 3;

}

/* Update stats file for unattended monitoring. */

static void write_stats_file(double bitmap_cvg, double eps)
{

	static double last_bcvg , last_eps;

	u8* fn = alloc_printf("%s/fuzzer_stats",out_dir);
	s32 fd;
	FILE* f;

	fd = open(fn,O_WRONLY | O_CREAT | O_TRUNC,0600);

	if (fd < 0)
		PFATAL("Unable to create '%s'",fn);

	ck_free(fn);

	f = fdopen(fd,"w");

	if (!f)
		PFATAL("fdopen() failed");

	/* Keep last values in case we're called from another context
	 where exec/sec stats and such are not readily available. */

	if (!bitmap_cvg && !eps)
	{
		bitmap_cvg = last_bcvg;
		eps = last_eps;
	}
	else
	{
		last_bcvg = bitmap_cvg;
		last_eps = eps;
	}

	fprintf(f, "start_time     : %llu\n"
			"last_update    : %llu\n"
			"fuzzer_pid     : %u\n"
			"cycles_done    : %llu\n"
			"execs_done     : %llu\n"
			"execs_per_sec  : %0.02f\n"
			"paths_total    : %u\n"
			"paths_favored  : %u\n"
			"paths_found    : %u\n"
			"paths_imported : %u\n"
			"max_depth      : %u\n"
			"cur_path       : %u\n"
			"pending_favs   : %u\n"
			"pending_total  : %u\n"
			"variable_paths : %u\n"
			"bitmap_cvg     : %0.02f%%\n"
			"unique_crashes : %llu\n"
			"unique_hangs   : %llu\n"
			"last_path      : %llu\n"
			"last_crash     : %llu\n"
			"last_hang      : %llu\n"
			"exec_timeout   : %u\n"
			"afl_banner     : %s\n"
			"afl_version    : " VERSION "\n"
			"command_line   : %s\n",
			start_time / 1000, get_cur_time() / 1000, getpid(),
			queue_cycle ? (queue_cycle - 1) : 0, total_execs, eps,
			queued_paths, queued_favored, queued_discovered, queued_imported,
			max_depth, current_entry, pending_favored, pending_not_fuzzed,
			queued_variable, bitmap_cvg, unique_crashes, unique_hangs,
			last_path_time / 1000, last_crash_time / 1000,
			last_hang_time / 1000, exec_tmout, use_banner, orig_cmdline);
	/* ignore errors */

	fclose(f);

}

/* Update the plot file if there is a reason to. */

static void maybe_update_plot_file(double bitmap_cvg, double eps)
{

	static u32 prev_qp , prev_pf , prev_pnf , prev_ce , prev_md;
	static u64 prev_qc , prev_uc , prev_uh;

	if (prev_qp == queued_paths && prev_pf == pending_favored
			&& prev_pnf == pending_not_fuzzed && prev_ce == current_entry
			&& prev_qc == queue_cycle && prev_uc == unique_crashes
			&& prev_uh == unique_hangs && prev_md == max_depth)
		return;

	prev_qp = queued_paths;
	prev_pf = pending_favored;
	prev_pnf = pending_not_fuzzed;
	prev_ce = current_entry;
	prev_qc = queue_cycle;
	prev_uc = unique_crashes;
	prev_uh = unique_hangs;
	prev_md = max_depth;

	/* Fields in the file:

	 unix_time, cycles_done, cur_path, paths_total, paths_not_fuzzed,
	 favored_not_fuzzed, unique_crashes, unique_hangs, max_depth,
	 execs_per_sec */

	fprintf(plot_file,
			"%llu, %llu, %u, %u, %u, %u, %0.02f%%, %llu, %llu, %u, %0.02f\n",
			get_cur_time() / 1000,queue_cycle - 1,current_entry,queued_paths,
			pending_not_fuzzed,pending_favored,bitmap_cvg,unique_crashes,
			unique_hangs,max_depth,eps); /* ignore errors */

	fflush(plot_file);

}

/* A helper function for maybe_delete_out_dir(), deleting all prefixed
 files in a directory. */

static u8 delete_files(u8* path, u8* prefix) //prefix是文件名的前缀,清楚一个目录中以prefix为前缀的文件
{

	DIR* d;
	struct dirent* d_ent;

	d = opendir(path);

	if (!d)
		return 0;

	while ((d_ent = readdir(d)))
	{

		if (d_ent->d_name [ 0 ] != '.'
				&& (!prefix || !strncmp(d_ent->d_name,prefix,strlen(prefix))))
		{ //判断前缀

			u8* fname = alloc_printf("%s/%s",path,d_ent->d_name);
			if (unlink(fname))
				PFATAL("Unable to delete '%s'",fname);
			ck_free(fname);

		}

	}

	closedir(d);

	return !!rmdir(path);

}

/* Get the number of runnable processes, with some simple smoothing. */

static double get_runnable_processes(void)
{

	static double res;

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)

	/* I don't see any portable sysctl or so that would quickly give us the
	 number of runnable processes; the 1-minute load average can be a
	 semi-decent approximation, though. */

	if (getloadavg(&res, 1) != 1) return 0;

#else

	/* On Linux, /proc/stat is probably the best way; load averages are
	 computed in funny ways and sometimes don't reflect extremely short-lived
	 processes well. */

	FILE* f = fopen("/proc/stat","r");
	u8 tmp [ 1024 ];
	u32 val = 0;

	if (!f)
		return 0;

	while (fgets(tmp,sizeof(tmp),f))
	{

		if (!strncmp(tmp,"procs_running ",14)
				|| !strncmp(tmp,"procs_blocked ",14))
			val += atoi(tmp + 14);

	}

	fclose(f);

	if (!res)
	{

		res = val;

	}
	else
	{

		res = res * (1.0 - 1.0 / AVG_SMOOTHING)
				+ ((double) val) * (1.0 / AVG_SMOOTHING);

	}

#endif /* ^(__APPLE__ || __FreeBSD__ || __OpenBSD__) */

	return res;

}

/* Delete the temporary directory used for in-place session resume. */

static void nuke_resume_dir(void)
{

	u8* fn;

	fn = alloc_printf("%s/_resume/.state/deterministic_done",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/_resume/.state/auto_extras",out_dir);
	if (delete_files(fn,"auto_"))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/_resume/.state/redundant_edges",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/_resume/.state/variable_behavior",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/_resume/.state",out_dir);
	if (rmdir(fn) && errno != ENOENT)
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/_resume",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	return;

	dir_cleanup_failed:

	FATAL("_resume directory cleanup failed");

}

/* Delete fuzzer output directory if we recognize it as ours, if the fuzzer
 is not currently running, and if the last run time isn't too great. */

static void maybe_delete_out_dir(void)
{

	FILE* f;
	u8 *fn = alloc_printf("%s/fuzzer_stats",out_dir);

	/* See if the output directory is locked. If yes, bail out. If not,
	 create a lock that will persist for the lifetime of the process
	 (this requires leaving the descriptor open).*/

	out_dir_fd = open(out_dir,O_RDONLY);
	if (out_dir_fd < 0)
		PFATAL("Unable to open '%s'",out_dir);

#ifndef __sun

	if (flock(out_dir_fd,LOCK_EX | LOCK_NB) && errno == EWOULDBLOCK)
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Looks like the job output directory is being actively used by another\n" "    instance of afl-fuzz. You will need to choose a different %s\n" "    or stop the other process first.\n",
				sync_id ? "fuzzer ID" : "output location");

		FATAL("Directory '%s' is in use",out_dir);

	}

#endif /* !__sun */

	f = fopen(fn,"r");

	if (f)
	{

		u64 start_time , last_update;

		if (fscanf(f,"start_time     : %llu\n"
				"last_update    : %llu\n",&start_time,&last_update) != 2)
			FATAL("Malformed data in '%s'",fn);

		fclose(f);

		/* Let's see how much work is at stake. */

		if (!in_place_resume && last_update - start_time > OUTPUT_GRACE * 60)
		{

			SAYF(
					"\n" cLRD "[-] " cRST "The job output directory already exists and contains the results of more\n" "    than %u minutes worth of fuzzing. To avoid data loss, afl-fuzz will *NOT*\n" "    automatically delete this data for you.\n\n"

					"    If you wish to start a new session, remove or rename the directory manually,\n" "    or specify a different output location for this job. To resume the old\n" "    session, put '-' as the input directory in the command line ('-i -') and\n" "    try again.\n",
					OUTPUT_GRACE);

			FATAL("At-risk data found in in '%s'",out_dir);

		}

	}

	ck_free(fn);

	/* The idea for in-place resume is pretty simple: we temporarily move the old
	 queue/ to a new location that gets deleted once import to the new queue/
	 is finished. If _resume/ already exists, the current queue/ may be
	 incomplete due to an earlier abort, so we want to use the old _resume/
	 dir instead, and we let rename() fail silently. */

	if (in_place_resume)
	{

		u8* orig_q = alloc_printf("%s/queue",out_dir);

		in_dir = alloc_printf("%s/_resume",out_dir);

		rename(orig_q,in_dir); /* Ignore errors */

		OKF("Output directory exists, will attempt session resume.");

		ck_free(orig_q);

	}
	else
	{

		OKF("Output directory exists but deemed OK to reuse.");

	}

	ACTF("Deleting old session data...");

	/* Okay, let's get the ball rolling! First, we need to get rid of the entries
	 in <out_dir>/.synced/.../id:*, if any are present. */

	fn = alloc_printf("%s/.synced",out_dir);
	if (delete_files(fn,NULL))
		goto dir_cleanup_failed;
	ck_free(fn);

	/* Next, we need to clean up <out_dir>/queue/.state/ subdirectories: */

	fn = alloc_printf("%s/queue/.state/deterministic_done",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/queue/.state/auto_extras",out_dir);
	if (delete_files(fn,"auto_"))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/queue/.state/redundant_edges",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/queue/.state/variable_behavior",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	/* Then, get rid of the .state subdirectory itself (should be empty by now)
	 and everything matching <out_dir>/queue/id:*. */

	fn = alloc_printf("%s/queue/.state",out_dir);
	if (rmdir(fn) && errno != ENOENT)
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/queue",out_dir);
	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

#ifdef XIAOSA
	//to remove the queue_trace_mini catalog
	fn = alloc_printf("%s/queue_trace_mini",out_dir);
	if (delete_files(fn,NULL))
		goto dir_cleanup_failed;
	ck_free(fn);

	//to remove the crash_trace_mini catalog
	fn = alloc_printf("%s/crash_trace_mini",out_dir);
	if (delete_files(fn,NULL))
		goto dir_cleanup_failed;
	ck_free(fn);
#endif

	/* All right, let's do <out_dir>/crashes/id:* and <out_dir>/hangs/id:*. */

	if (!in_place_resume)
	{

		fn = alloc_printf("%s/crashes/README.txt",out_dir);
		unlink(fn); /* Ignore errors */
		ck_free(fn);

	}

	fn = alloc_printf("%s/crashes",out_dir);

	/* Make backup of the crashes directory if it's not empty and if we're
	 doing in-place resume. */

	if (in_place_resume && rmdir(fn))
	{

		time_t cur_t = time(0);
		struct tm* t = localtime(&cur_t);

#ifndef SIMPLE_FILES

		u8* nfn = alloc_printf("%s.%04u-%02u-%02u-%02u:%02u:%02u",fn,
				t->tm_year + 1900,t->tm_mon + 1,t->tm_mday,t->tm_hour,t->tm_min,
				t->tm_sec);

#else

		u8* nfn = alloc_printf("%s_%04u%02u%02u%02u%02u%02u", fn,
				t->tm_year + 1900, t->tm_mon + 1, t->tm_mday,
				t->tm_hour, t->tm_min, t->tm_sec);

#endif /* ^!SIMPLE_FILES */

		rename(fn,nfn); /* Ignore errors. */
		ck_free(nfn);

	}

	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/hangs",out_dir);

	/* Backup hangs, too. */

	if (in_place_resume && rmdir(fn))
	{

		time_t cur_t = time(0);
		struct tm* t = localtime(&cur_t);

#ifndef SIMPLE_FILES

		u8* nfn = alloc_printf("%s.%04u-%02u-%02u-%02u:%02u:%02u",fn,
				t->tm_year + 1900,t->tm_mon + 1,t->tm_mday,t->tm_hour,t->tm_min,
				t->tm_sec);

#else

		u8* nfn = alloc_printf("%s_%04u%02u%02u%02u%02u%02u", fn,
				t->tm_year + 1900, t->tm_mon + 1, t->tm_mday,
				t->tm_hour, t->tm_min, t->tm_sec);

#endif /* ^!SIMPLE_FILES */

		rename(fn,nfn); /* Ignore errors. */
		ck_free(nfn);

	}

	if (delete_files(fn,CASE_PREFIX))
		goto dir_cleanup_failed;
	ck_free(fn);

	/* And now, for some finishing touches. */

	fn = alloc_printf("%s/.cur_input",out_dir);
	if (unlink(fn) && errno != ENOENT)
		goto dir_cleanup_failed;
	ck_free(fn);

	fn = alloc_printf("%s/fuzz_bitmap",out_dir);
	if (unlink(fn) && errno != ENOENT)
		goto dir_cleanup_failed;
	ck_free(fn);

	if (!in_place_resume)
	{
		fn = alloc_printf("%s/fuzzer_stats",out_dir);
		if (unlink(fn) && errno != ENOENT)
			goto dir_cleanup_failed;
		ck_free(fn);
	}

	fn = alloc_printf("%s/plot_data",out_dir);
	if (unlink(fn) && errno != ENOENT)
		goto dir_cleanup_failed;
	ck_free(fn);

	OKF("Output dir cleanup successful.");

	/* Wow... is that all? If yes, celebrate! */

	return;

	dir_cleanup_failed:

	SAYF(
			"\n" cLRD "[-] " cRST "Whoops, the fuzzer tried to reuse your output directory, but bumped into\n" "    some files that shouldn't be there or that couldn't be removed - so it\n" "    decided to abort! This happened while processing this path:\n\n"

			"    %s\n\n" "    Please examine and manually delete the files, or specify a different\n" "    output location for the tool.\n",
			fn);

	FATAL("Output directory cleanup failed");

}

static void check_term_size(void);

/* A spiffy retro stats screen! This is called every stats_update_freq
 execve() calls, plus in several other circumstances. */

static void show_stats(void)
{

	static u64 last_stats_ms , last_plot_ms , last_ms , last_execs;
	static double avg_exec;
	double t_byte_ratio;

	u64 cur_ms;
	u32 t_bytes , t_bits; //t_bits表示出现过的元组数量(考虑滚筒)  t_bytes表示出现过的元组数量(没有滚筒)

	u32 banner_len , banner_pad;
	u8 tmp [ 256 ];

	cur_ms = get_cur_time();

	/* If not enough time has passed since last UI update, bail out. */

	if (cur_ms - last_ms < 1000 / UI_TARGET_HZ)
		return;

	/* Check if we're past the 10 minute mark. */

	if (cur_ms - start_time > 10 * 60 * 1000)
		run_over10m = 1;

	/* Calculate smoothed exec speed stats. */

	if (!last_execs)
	{

		avg_exec = ((double) total_execs) * 1000 / (cur_ms - start_time);

	}
	else
	{

		double cur_avg = ((double) (total_execs - last_execs)) * 1000
				/ (cur_ms - last_ms);

		/* If there is a dramatic (5x+) jump in speed, reset the indicator
		 more quickly. */

		if (cur_avg * 5 < avg_exec || cur_avg / 5 > avg_exec)
			avg_exec = cur_avg;

		avg_exec = avg_exec * (1.0 - 1.0 / AVG_SMOOTHING)
				+ cur_avg * (1.0 / AVG_SMOOTHING);

	}

	last_ms = cur_ms;
	last_execs = total_execs;

	/* Tell the callers when to contact us (as measured in execs). */

	stats_update_freq = avg_exec / (UI_TARGET_HZ * 10);
	if (!stats_update_freq)
		stats_update_freq = 1;

	/* Do some bitmap stats. */

	t_bytes = count_non_255_bytes(virgin_bits);
	t_byte_ratio = ((double) t_bytes * 100) / MAP_SIZE;

	/* Roughly every minute, update fuzzer stats and save auto tokens. */

	if (cur_ms - last_stats_ms > STATS_UPDATE_SEC * 1000)
	{

		last_stats_ms = cur_ms;
		write_stats_file(t_byte_ratio,avg_exec);
		save_auto();
		write_bitmap();

	}

	/* Every now and then, write plot data. */

	if (cur_ms - last_plot_ms > PLOT_UPDATE_SEC * 1000)
	{

		last_plot_ms = cur_ms;
		maybe_update_plot_file(t_byte_ratio,avg_exec);

	}

	/* Honor AFL_EXIT_WHEN_DONE. */

	if (!dumb_mode && cycles_wo_finds > 20 && !pending_not_fuzzed
			&& getenv("AFL_EXIT_WHEN_DONE"))
		stop_soon = 2;

	/* If we're not on TTY, bail out. */

	if (not_on_tty)
		return;

	/* Compute some mildly useful bitmap stats. */

	t_bits = (MAP_SIZE << 3) - count_bits(virgin_bits); //65536*8位,减去virgin_bits中1的数量,即没有出现过的元组关系数量,考虑了滚筒

	/* Now, for the visuals... */

	if (clear_screen)
	{

		SAYF(TERM_CLEAR CURSOR_HIDE);
		clear_screen = 0;

		check_term_size();

	}

	SAYF(TERM_HOME);

//yyy
#ifndef XIAOSA
	if (term_too_small)
	{

		SAYF(
				cBRI "Your terminal is too small to display the UI.\n" "Please resize terminal window to at least 80x25.\n" cNOR);
		return;

	}
#endif

	/* Let's start by drawing a centered banner. */

	banner_len = (crash_mode ? 24 : 22) + strlen(VERSION) + strlen(use_banner);
	banner_pad = (80 - banner_len) / 2;
	memset(tmp,' ',banner_pad);

sprintf(tmp + banner_pad, "%s " cLCY VERSION cLGN
          " (%s)",  crash_mode ? cPIN "peruvian were-rabbit" : 
          cYEL "american fuzzy lop", use_banner);

  																									SAYF("\n%s\n\n",tmp);

	/* "Handy" shortcuts for drawing boxes... */

#define bSTG    bSTART cGRA
#define bH2     bH bH
#define bH5     bH2 bH2 bH
#define bH10    bH5 bH5
#define bH20    bH10 bH10
#define bH30    bH20 bH10
#define SP5     "     "
#define SP10    SP5 SP5
#define SP20    SP10 SP10

	/* Lord, forgive me this. */

	SAYF(
			SET_G1 bSTG bLT bH bSTOP cCYA " process timing " bSTG bH30 bH5 bH2 bHB bH bSTOP cCYA " overall results " bSTG bH5 bRT "\n");

	if (dumb_mode)
	{

		strcpy(tmp,cNOR);

	}
	else
	{

		/* First queue cycle: don't stop now! */
		if (queue_cycle == 1)
			strcpy(tmp,cMGN);
		else

		/* Subsequent cycles, but we're still making finds. */
		if (cycles_wo_finds < 3)
			strcpy(tmp,cYEL);
		else

		/* No finds for a long time and no test cases to try. */
		if (cycles_wo_finds > 20 && !pending_not_fuzzed)
			strcpy(tmp,cLGN);

		/* Default: cautiously OK to stop? */
		else
			strcpy(tmp,cLBL);

	}

	SAYF(
			bV bSTOP "        run time : " cNOR "%-34s " bSTG bV bSTOP "  cycles done : %s%-5s  " bSTG bV "\n",
			DTD(cur_ms,start_time),tmp,DI(queue_cycle - 1));

	/* We want to warn people about not seeing new paths after a full cycle,
	 except when resuming fuzzing or running in non-instrumented mode. */

	if (!dumb_mode
			&& (last_path_time || resuming_fuzz || queue_cycle == 1 || in_bitmap
					|| crash_mode))
	{

		SAYF(bV bSTOP "   last new path : " cNOR "%-34s ",
				DTD(cur_ms,last_path_time));

	}
	else
	{

		if (dumb_mode)

			SAYF(
					bV bSTOP "   last new path : " cPIN "n/a" cNOR " (non-instrumented mode)        ");

		else
			//插桩模式
			SAYF(
					bV bSTOP "   last new path : " cNOR "none yet " cLRD "(odd, check syntax!)      ");

	}

	SAYF(bSTG bV bSTOP "  total paths : " cNOR "%-5s  " bSTG bV "\n",
			DI(queued_paths));

	/* Highlight crashes in red if found, denote going over the KEEP_UNIQUE_CRASH
	 limit with a '+' appended to the count. */

	sprintf(tmp,"%s%s",DI(unique_crashes),
			(unique_crashes >= KEEP_UNIQUE_CRASH) ? "+" : "");

	SAYF(
			bV bSTOP " last uniq crash : " cNOR "%-34s " bSTG bV bSTOP " uniq crashes : %s%-6s " bSTG bV "\n",
			DTD(cur_ms,last_crash_time),unique_crashes ? cLRD : cNOR,tmp);

	sprintf(tmp,"%s%s",DI(unique_hangs),
			(unique_hangs >= KEEP_UNIQUE_HANG) ? "+" : "");

	SAYF(
			bV bSTOP "  last uniq hang : " cNOR "%-34s " bSTG bV bSTOP "   uniq hangs : " cNOR "%-6s " bSTG bV "\n",
			DTD(cur_ms,last_hang_time),tmp);

	SAYF(
			bVR bH bSTOP cCYA " cycle progress " bSTG bH20 bHB bH bSTOP cCYA " map coverage " bSTG bH bHT bH20 bH2 bH bVL "\n");

	/* This gets funny because we want to print several variable-length variables
	 together, but then cram them into a fixed-width field - so we need to
	 put them in a temporary buffer first. */

	sprintf(tmp,"%s%s (%0.02f%%)",DI(current_entry),
			queue_cur->favored ? "" : "*",
			((double )current_entry * 100) / queued_paths);

	SAYF(bV bSTOP "  now processing : " cNOR "%-17s " bSTG bV bSTOP,tmp);

	sprintf(tmp,"%s (%0.02f%%)",DI(t_bytes),t_byte_ratio);

	SAYF("    map density : %s%-21s " bSTG bV "\n",
			t_byte_ratio > 70 ? cLRD : ((t_bytes < 200 && !dumb_mode) ? cPIN : cNOR),
			tmp);

	sprintf(tmp,"%s (%0.02f%%)",DI(cur_skipped_paths),
			((double )cur_skipped_paths * 100) / queued_paths);

	SAYF(bV bSTOP " paths timed out : " cNOR "%-17s " bSTG bV,tmp);

	sprintf(tmp,"%0.02f bits/tuple",
			t_bytes ? (((double )t_bits) / t_bytes) : 0);

	SAYF(bSTOP " count coverage : " cNOR "%-21s " bSTG bV "\n",tmp);

	SAYF(
			bVR bH bSTOP cCYA " stage progress " bSTG bH20 bX bH bSTOP cCYA " findings in depth " bSTG bH20 bVL "\n");

	sprintf(tmp,"%s (%0.02f%%)",DI(queued_favored),
			((double )queued_favored) * 100 / queued_paths);

	/* Yeah... it's still going on... halp? */

	SAYF(
			bV bSTOP "  now trying : " cNOR "%-21s " bSTG bV bSTOP " favored paths : " cNOR "%-22s " bSTG bV "\n",
			stage_name,tmp);

	if (!stage_max)
	{

		sprintf(tmp,"%s/-",DI(stage_cur));

	}
	else
	{

		sprintf(tmp,"%s/%s (%0.02f%%)",DI(stage_cur),DI(stage_max),
				((double )stage_cur) * 100 / stage_max);

	}

	SAYF(bV bSTOP " stage execs : " cNOR "%-21s " bSTG bV bSTOP,tmp);

	sprintf(tmp,"%s (%0.02f%%)",DI(queued_with_cov),
			((double )queued_with_cov) * 100 / queued_paths);

	SAYF("  new edges on : " cNOR "%-22s " bSTG bV "\n",tmp);

	sprintf(tmp,"%s (%s%s unique)",DI(total_crashes),DI(unique_crashes),
			(unique_crashes >= KEEP_UNIQUE_CRASH) ? "+" : "");

	if (crash_mode)
	{

		SAYF(
				bV bSTOP " total execs : " cNOR "%-21s " bSTG bV bSTOP "   new crashes : %s%-22s " bSTG bV "\n",
				DI(total_execs),unique_crashes ? cLRD : cNOR,tmp);

	}
	else
	{

		SAYF(
				bV bSTOP " total execs : " cNOR "%-21s " bSTG bV bSTOP " total crashes : %s%-22s " bSTG bV "\n",
				DI(total_execs),unique_crashes ? cLRD : cNOR,tmp);

	}

	/* Show a warning about slow execution. */

	if (avg_exec < 100)
	{

		sprintf(tmp,"%s/sec (%s)",DF(avg_exec),
				avg_exec < 20 ? "zzzz..." : "slow!");

		SAYF(bV bSTOP "  exec speed : " cLRD "%-21s ",tmp);

	}
	else
	{

		sprintf(tmp,"%s/sec",DF(avg_exec));
		SAYF(bV bSTOP "  exec speed : " cNOR "%-21s ",tmp);

	}

	sprintf(tmp,"%s (%s%s unique)",DI(total_hangs),DI(unique_hangs),
			(unique_hangs >= KEEP_UNIQUE_HANG) ? "+" : "");

	SAYF(bSTG bV bSTOP "   total hangs : " cNOR "%-22s " bSTG bV "\n",tmp);

	/* Aaaalmost there... hold on! */

	SAYF(
			bVR bH cCYA bSTOP " fuzzing strategy yields " bSTG bH10 bH bHT bH10 bH5 bHB bH bSTOP cCYA " path geometry " bSTG bH5 bH2 bH bVL "\n");

	if (skip_deterministic)
	{

		strcpy(tmp,"n/a, n/a, n/a");

	}
	else
	{

		sprintf(tmp,"%s/%s, %s/%s, %s/%s",DI(stage_finds [ STAGE_FLIP1 ]),
				DI(stage_cycles [ STAGE_FLIP1 ]),
				DI(stage_finds [ STAGE_FLIP2 ]),
				DI(stage_cycles [ STAGE_FLIP2 ]),
				DI(stage_finds [ STAGE_FLIP4 ]),
				DI(stage_cycles [ STAGE_FLIP4 ]));

	}

	SAYF(
			bV bSTOP "   bit flips : " cNOR "%-37s " bSTG bV bSTOP "    levels : " cNOR "%-10s " bSTG bV "\n",
			tmp,DI(max_depth));

	if (!skip_deterministic)
		sprintf(tmp,"%s/%s, %s/%s, %s/%s",DI(stage_finds [ STAGE_FLIP8 ]),
				DI(stage_cycles [ STAGE_FLIP8 ]),
				DI(stage_finds [ STAGE_FLIP16 ]),
				DI(stage_cycles [ STAGE_FLIP16 ]),
				DI(stage_finds [ STAGE_FLIP32 ]),
				DI(stage_cycles [ STAGE_FLIP32 ]));

	SAYF(
			bV bSTOP "  byte flips : " cNOR "%-37s " bSTG bV bSTOP "   pending : " cNOR "%-10s " bSTG bV "\n",
			tmp,DI(pending_not_fuzzed));

	if (!skip_deterministic)
		sprintf(tmp,"%s/%s, %s/%s, %s/%s",DI(stage_finds [ STAGE_ARITH8 ]),
				DI(stage_cycles [ STAGE_ARITH8 ]),
				DI(stage_finds [ STAGE_ARITH16 ]),
				DI(stage_cycles [ STAGE_ARITH16 ]),
				DI(stage_finds [ STAGE_ARITH32 ]),
				DI(stage_cycles [ STAGE_ARITH32 ]));

	SAYF(
			bV bSTOP " arithmetics : " cNOR "%-37s " bSTG bV bSTOP "  pend fav : " cNOR "%-10s " bSTG bV "\n",
			tmp,DI(pending_favored));

	if (!skip_deterministic)
		sprintf(tmp,"%s/%s, %s/%s, %s/%s",DI(stage_finds [ STAGE_INTEREST8 ]),
				DI(stage_cycles [ STAGE_INTEREST8 ]),
				DI(stage_finds [ STAGE_INTEREST16 ]),
				DI(stage_cycles [ STAGE_INTEREST16 ]),
				DI(stage_finds [ STAGE_INTEREST32 ]),
				DI(stage_cycles [ STAGE_INTEREST32 ]));

	SAYF(
			bV bSTOP "  known ints : " cNOR "%-37s " bSTG bV bSTOP " own finds : " cNOR "%-10s " bSTG bV "\n",
			tmp,DI(queued_discovered));

	if (!skip_deterministic)
		sprintf(tmp,"%s/%s, %s/%s, %s/%s",DI(stage_finds [ STAGE_EXTRAS_UO ]),
				DI(stage_cycles [ STAGE_EXTRAS_UO ]),
				DI(stage_finds [ STAGE_EXTRAS_UI ]),
				DI(stage_cycles [ STAGE_EXTRAS_UI ]),
				DI(stage_finds [ STAGE_EXTRAS_AO ]),
				DI(stage_cycles [ STAGE_EXTRAS_AO ]));

	SAYF(
			bV bSTOP "  dictionary : " cNOR "%-37s " bSTG bV bSTOP "  imported : " cNOR "%-10s " bSTG bV "\n",
			tmp,sync_id ? DI(queued_imported) : (u8* )"n/a");

	sprintf(tmp,"%s/%s, %s/%s",DI(stage_finds [ STAGE_HAVOC ]),
			DI(stage_cycles [ STAGE_HAVOC ]),DI(stage_finds [ STAGE_SPLICE ]),
			DI(stage_cycles [ STAGE_SPLICE ]));

	SAYF(
			bV bSTOP "       havoc : " cNOR "%-37s " bSTG bV bSTOP "  variable : %s%-10s " bSTG bV "\n",
			tmp,queued_variable ? cLRD : cNOR,
			no_var_check ? (u8* )"n/a" : DI(queued_variable));

	if (!bytes_trim_out)
	{

		sprintf(tmp,"n/a, ");

	}
	else
	{

		sprintf(tmp,"%0.02f%%/%s, ",
				((double )(bytes_trim_in - bytes_trim_out)) * 100
						/ bytes_trim_in,DI(trim_execs));

	}

	if (!blocks_eff_total)
	{

		u8 tmp2 [ 128 ];

		sprintf(tmp2,"n/a");
		strcat(tmp,tmp2);

	}
	else
	{

		u8 tmp2 [ 128 ];

		sprintf(tmp2,"%0.02f%%",
				((double )(blocks_eff_total - blocks_eff_select)) * 100
						/ blocks_eff_total);

		strcat(tmp,tmp2);

	}

	SAYF(
			bV bSTOP "        trim : " cNOR "%-37s " bSTG bVR bH20 bH2 bH2 bRB "\n" bLB bH30 bH20 bH2 bH bRB bSTOP cRST RESET_G1,
			tmp);

	/* Provide some CPU utilization stats. */

	if (cpu_core_count)
	{

		double cur_runnable = get_runnable_processes();
		u32 cur_utilization = cur_runnable * 100 / cpu_core_count;

		u8* cpu_color = cCYA;

		/* If we could still run one or more processes, use green. */

		if (cpu_core_count > 1 && cur_runnable + 1 <= cpu_core_count)
			cpu_color = cLGN;

		/* If we're clearly oversubscribed, use red. */

		if (!no_cpu_meter_red && cur_utilization >= 150)
			cpu_color = cLRD;

		SAYF(SP10 cGRA "   [cpu:%s%3u%%" cGRA "]\r" cRST,cpu_color,
				cur_utilization < 999 ? cur_utilization : 999);

	}
	else
		SAYF("\r");

	/* Hallelujah! */

	fflush(0);

}

/* Display quick statistics at the end of processing the input directory,
 plus a bunch of warnings. Some calibration stuff also ended up here,
 along with several hardcoded constants. Maybe clean up eventually. */

static void show_init_stats(void)
{

	struct queue_entry* q = queue;
	u32 min_bits = 0 , max_bits = 0;
	u64 min_us = 0 , max_us = 0;
	u64 avg_us = 0;
	u32 max_len = 0;

	if (total_cal_cycles)
		avg_us = total_cal_us / total_cal_cycles;

	while (q)
	{

		if (!min_us || q->exec_us < min_us)
			min_us = q->exec_us;
		if (q->exec_us > max_us)
			max_us = q->exec_us;

		if (!min_bits || q->bitmap_size < min_bits)
			min_bits = q->bitmap_size;
		if (q->bitmap_size > max_bits)
			max_bits = q->bitmap_size;

		if (q->len > max_len)
			max_len = q->len;

		q = q->next;

	}

	SAYF("\n");

	if (avg_us > (qemu_mode ? 50000 : 10000))
		WARNF(cLRD "The target binary is pretty slow! See %s/perf_tips.txt.",
				doc_path);

	/* Let's keep things moving with slow binaries. */

	if (avg_us > 50000)
		havoc_div = 10; /* 0-19 execs/sec   */
	else if (avg_us > 20000)
		havoc_div = 5; /* 20-49 execs/sec  */
	else if (avg_us > 10000)
		havoc_div = 2; /* 50-100 execs/sec */

	if (!resuming_fuzz)
	{

		if (max_len > 50 * 1024)
			WARNF(cLRD "Some test cases are huge (%s) - see %s/perf_tips.txt!",
					DMS(max_len),doc_path);
		else if (max_len > 10 * 1024)
			WARNF("Some test cases are big (%s) - see %s/perf_tips.txt.",
					DMS(max_len),doc_path);

		if (useless_at_start && !in_bitmap)
			WARNF(
					cLRD "Some test cases look useless. Consider using a smaller set.");

		if (queued_paths > 100)
			WARNF(
					cLRD "You probably have far too many input files! Consider trimming down.");
		else if (queued_paths > 20)
			WARNF("You have lots of input files; try starting small.");

	}

	OKF(
			"Here are some useful stats:\n\n"
			cGRA "    Test case count : " cNOR "%u favored, %u variable, %u total\n" cGRA "       Bitmap range : " cNOR "%u to %u bits (average: %0.02f bits)\n" cGRA "        Exec timing : " cNOR "%s to %s us (average: %s us)\n",
			queued_favored,queued_variable,queued_paths,min_bits,max_bits,
			((double )total_bitmap_size)
					/ (total_bitmap_entries ? total_bitmap_entries : 1),
			DI(min_us),DI(max_us),DI(avg_us));

	if (!timeout_given)
	{

		/* Figure out the appropriate timeout. The basic idea is: 5x average or
		 1x max, rounded up to EXEC_TM_ROUND ms and capped at 1 second.

		 If the program is slow, the multiplier is lowered to 2x or 3x, because
		 random scheduler jitter is less likely to have any impact, and because
		 our patience is wearing thin =) */

		if (avg_us > 50000)
			exec_tmout = avg_us * 2 / 1000;
		else if (avg_us > 10000)
			exec_tmout = avg_us * 3 / 1000;
		else
			exec_tmout = avg_us * 5 / 1000;

		exec_tmout = MAX(exec_tmout,max_us / 1000);
		exec_tmout = (exec_tmout + EXEC_TM_ROUND) / EXEC_TM_ROUND
				* EXEC_TM_ROUND;

		if (exec_tmout > EXEC_TIMEOUT)
			exec_tmout = EXEC_TIMEOUT;

		ACTF("No -t option specified, so I'll use exec timeout of %u ms.",
				exec_tmout);

		timeout_given = 1;

	}
	else if (timeout_given == 3)
	{

		ACTF("Applying timeout settings from resumed session (%u ms).",
				exec_tmout);

	}

	OKF("All set and ready to roll!");

}

/* Find first power of two greater or equal to val. */

static u32 next_p2(u32 val)
{

	u32 ret = 1;
	while (val > ret)
		ret <<= 1;
	return ret;

}

/* Trim all new test cases to save cycles when doing deterministic checks. The
 trimmer uses power-of-two(2的指数) increments somewhere between 1/16 and 1/1024 of
 file size, to keep the stage short and sweet. */

static u8 trim_case(char** argv, struct queue_entry* q, u8* in_buf)
{

	static u8 tmp [ 64 ];
	static u8 clean_trace [ MAP_SIZE ];

	u8 needs_write = 0 , fault = 0;
	u32 trim_exec = 0;
	u32 remove_len;
	u32 len_p2;

	/* Although the trimmer will be less useful when variable behavior is
	 detected, it will still work to some extent, so we don't check for
	 this. */

	if (q->len < 5)
		return 0;

	stage_name = tmp;    //等于指针
	bytes_trim_in += q->len;

	/* Select initial chunk len, starting with large steps. */

	len_p2 = next_p2(q->len); //和2的幂次方对应,向上取
	//这个是经验性的操作,步长
	remove_len = MAX(len_p2 / TRIM_START_STEPS,TRIM_MIN_BYTES); //TRIM_START_STEPS is ,  TRIM_MIN_BYTES is

	/* Continue until the number of steps gets too high or the stepover
	 gets too small. */

	while (remove_len >= MAX(len_p2 / TRIM_END_STEPS,TRIM_MIN_BYTES))
	{ //这个是怎么trim的,原理? TRIM_END_STEPS is 1024

		u32 remove_pos = remove_len; //准备保留的位数

		sprintf(tmp,"trim %s/%s",DI(remove_len),DI(remove_len));

		stage_cur = 0;
		stage_max = q->len / remove_len; //循环次数

		while (remove_pos < q->len)
		{ //每次q->len长度减少remove_pos,q指向queue/id:000000,orig:a

			u32 trim_avail = MIN(remove_len,q->len - remove_pos); //准备缩减的字节数量
			u32 cksum;

			write_with_gap(in_buf,q->len,remove_pos,trim_avail); //cur_input中删除了trim_avail个字节的内容
																 //一般是4个字节,不足4个字节时不补足4个字节
			fault = run_target(argv);
			trim_execs++;

			if (stop_soon || fault == FAULT_ERROR)
				goto abort_trimming;
			//如果不能运行了

			/* Note that we don't keep track of crashes or hangs here; maybe TODO? */

			cksum = hash32(trace_bits,MAP_SIZE,HASH_CONST);

			/* If the deletion had no impact on the trace, make it permanent. This
			 isn't perfect for variable-path inputs, but we're just making a
			 best-effort pass, so it's not a big deal if we end up with false
			 negatives every now and then. */

			if (cksum == q->exec_cksum)//修正后的执行轨迹hash和初始的执行轨迹hash,是完全准确的
			{ //说明执行轨迹没有变换,

				u32 move_tail = q->len - remove_pos - trim_avail;

				q->len -= trim_avail;
				len_p2 = next_p2(q->len); //补成2进制完整数

				memmove(in_buf + remove_pos,in_buf + remove_pos + trim_avail,
						move_tail);

				/* Let's save a clean trace, which will be needed by
				 update_bitmap_score once we're done with the trimming stuff. */

				if (!needs_write)
				{

					needs_write = 1;
					memcpy(clean_trace,trace_bits,MAP_SIZE); //保护一下原来的trace_bit

				}

			}
			else
				remove_pos += remove_len;

			/* Since this can be slow, update the screen every now and then. */

			if (!(trim_exec++ % stats_update_freq))
				show_stats();
			stage_cur++;

		}

		remove_len >>= 1;

	}

	/* If we have made changes to in_buf, we also need to update the on-disk
	 version of the test case. */

	if (needs_write)
	{	//将trim后的信息重新覆盖写入

		s32 fd;

		unlink(q->fname); /* ignore errors */

		fd = open(q->fname,O_WRONLY | O_CREAT | O_EXCL,0600);

		if (fd < 0)
			PFATAL("Unable to create '%s'",q->fname);

		ck_write(fd,in_buf,q->len,q->fname); //写入到/output/queue下
		close(fd);

		memcpy(trace_bits,clean_trace,MAP_SIZE);
		update_bitmap_score(q); //打分,更改top_rate数组,因为top_rate数组指向的内容都是queue目录上的
		//这里搞这个函数是不是,是因为长度会变化,所以判断标准也会变化.
	}

	abort_trimming:

	bytes_trim_out += q->len;
	return fault; //最后一个测试用例的执行结果

}

/* Write a modified test case, run program, process results. Handle
 error conditions, returning 1 if it's time to bail out. This is
 a helper function for fuzz_one(). */

static u8 common_fuzz_stuff(char** argv, u8* out_buf, u32 len)
{

	u8 fault;

	if (post_handler)
	{

		out_buf = post_handler(out_buf,&len);
		if (!out_buf || !len)
			return 0;

	}

	write_to_testcase(out_buf,len);

	fault = run_target(argv);

	if (stop_soon)
		return 1;

	if (fault == FAULT_HANG)
	{

		if (subseq_hangs++ > HANG_LIMIT)
		{ //挂起有一个上限
			cur_skipped_paths++;
			return 1;
		}

	}
	else
		subseq_hangs = 0;

	/* Users can hit us with SIGUSR1 to request the current input
	 to be abandoned. */

	if (skip_requested)
	{

		skip_requested = 0;
		cur_skipped_paths++;
		return 1;

	}

	/* This handles FAULT_ERROR for us: */

	queued_discovered += save_if_interesting(argv,out_buf,len,fault);

	if (!(stage_cur % stats_update_freq) || stage_cur + 1 == stage_max)
		show_stats();

	return 0;

}

/* Helper to choose random block len for block operations in fuzz_one().
 Doesn't return zero, provided that max_len is > 0. */

static u32 choose_block_len(u32 limit)
{

	u32 min_value , max_value;
	u32 rlim = MIN(queue_cycle,3);

	if (!run_over10m)
		rlim = 1;

	switch (UR(rlim))
	{

		case 0 :
			min_value = 1;
			max_value = HAVOC_BLK_SMALL;
			break;

		case 1 :
			min_value = HAVOC_BLK_SMALL;
			max_value = HAVOC_BLK_MEDIUM;
			break;

		default :
			min_value = HAVOC_BLK_MEDIUM;
			max_value = HAVOC_BLK_LARGE;

	}

	if (min_value >= limit)
		min_value = 1;

	return min_value + UR(MIN(max_value, limit) - min_value + 1);

}

/* Calculate case desirability score to adjust the length of havoc fuzzing.
 A helper function for fuzz_one(). Maybe some of these constants should
 go into config.h. */

static u32 calculate_score(struct queue_entry* q)
{

	u32 avg_exec_us = total_cal_us / total_cal_cycles;
	u32 avg_bitmap_size = total_bitmap_size / total_bitmap_entries;
	u32 perf_score = 100;

	/* Adjust score based on execution speed of this path, compared to the
	 global average. Multiplier ranges from 0.1x to 3x. Fast inputs are
	 less expensive to fuzz, so we're giving them more air time. */
	//从执行时间的角度考虑问题
	if (q->exec_us * 0.1 > avg_exec_us)
		perf_score = 10;
	else if (q->exec_us * 0.25 > avg_exec_us)
		perf_score = 25;
	else if (q->exec_us * 0.5 > avg_exec_us)
		perf_score = 50;
	else if (q->exec_us * 0.75 > avg_exec_us)
		perf_score = 75;
	else if (q->exec_us * 4 < avg_exec_us)
		perf_score = 300;
	else if (q->exec_us * 3 < avg_exec_us)
		perf_score = 200;
	else if (q->exec_us * 2 < avg_exec_us)
		perf_score = 150;

	/* Adjust score based on bitmap size. The working theory is that better
	 coverage translates to better targets. Multiplier from 0.25x to 3x. */
	//从基本块数量的角度考虑问题
	if (q->bitmap_size * 0.3 > avg_bitmap_size)
		perf_score *= 3;
	else if (q->bitmap_size * 0.5 > avg_bitmap_size)
		perf_score *= 2;
	else if (q->bitmap_size * 0.75 > avg_bitmap_size)
		perf_score *= 1.5;
	else if (q->bitmap_size * 3 < avg_bitmap_size)
		perf_score *= 0.25;
	else if (q->bitmap_size * 2 < avg_bitmap_size)
		perf_score *= 0.5;
	else if (q->bitmap_size * 1.5 < avg_bitmap_size)
		perf_score *= 0.75;

	/* Adjust score based on handicap. Handicap is proportional to how late
	 in the game we learned about this path. Latecomers are allowed to run
	 for a bit longer until they catch up with the rest. */
	//handicap是大循环的次数,越后面产生的多跑一会,表示这个测试用例难跑出来.
	if (q->handicap >= 4)
	{
		perf_score *= 4;
		q->handicap -= 4; //每次乘以4之后减去4.
	}
	else if (q->handicap)
	{

		perf_score *= 2;
		q->handicap--;

	}

	/* Final adjustment based on input depth, under the assumption that fuzzing
	 deeper test cases is more likely to reveal stuff that can't be
	 discovered with traditional fuzzers. */

	switch (q->depth)
	{

		case 0 ... 3 :
			break;
		case 4 ... 7 :
			perf_score *= 2;
			break;
		case 8 ... 13 :
			perf_score *= 4;
			break;
		case 14 ... 25 :
			perf_score *= 6;
			break;
		default :
			perf_score *= 8;

	}

	/* Make sure that we don't go over limit. */

	if (perf_score > HAVOC_MAX_MULT * 100)
		perf_score = HAVOC_MAX_MULT * 100;

	return perf_score;

}

/* Helper function to see if a particular change (xor_val = old ^ new) could
 be a product of deterministic bit flips with the lengths and stepovers
 attempted by afl-fuzz. This is used to avoid dupes in some of the
 deterministic fuzzing operations that follow bit flips. We also
 return 1 if xor_val is zero, which implies that the old and attempted new
 values are identical and the exec would be a waste of time. */

static u8 could_be_bitflip(u32 xor_val)
{ //参数是异或后的值

	u32 sh = 0;

	if (!xor_val)
		return 1; //一样的值,异或后是0

	/* Shift left until first bit set. */

	while (!(xor_val & 1)) //统计右边0的位数,然后右移
	{
		sh++;
		xor_val >>= 1;
	}

	/* 1-, 2-, and 4-bit patterns are OK anywhere. */

	if (xor_val == 1 || xor_val == 3 || xor_val == 15) //如果1,3,15,表示之前是有1/2/4位取反,是bitflip阶段
		return 1;

	/* 8-, 16-, and 32-bit patterns are OK only if shift factor is
	 divisible by 8, since that's the stepover for these ops. */

	if (sh & 7) //如果sh为0 8 16 24 32,即是一个字节单位的变换,还要进一步判断是是否为8/16/32位bitflip阶段
		return 0;

	if (xor_val == 0xff || xor_val == 0xffff || xor_val == 0xffffffff) //判断是否为8/16/32位bitflip阶段
		return 1;

	return 0;

}

/* Helper function to see if a particular value is reachable through
 arithmetic operations. Used for similar purposes. */

static u8 could_be_arith(u32 old_val, u32 new_val, u8 blen)
{

	u32 i , ov = 0 , nv = 0 , diffs = 0;

	if (old_val == new_val)
		return 1;

	/* See if one-byte adjustments to any byte could produce this result. */

	for (i = 0; i < blen; i++)
	{

		u8 a = old_val >> (8 * i) , b = new_val >> (8 * i);

		if (a != b)
		{
			diffs++;
			ov = a;
			nv = b;
		}

	}

	/* If only one byte differs and the values are within range, return 1. */

	if (diffs == 1)
	{

		if ((u8) (ov - nv) <= ARITH_MAX || (u8) (nv - ov) <= ARITH_MAX)
			return 1;

	}

	if (blen == 1)
		return 0;

	/* See if two-byte adjustments to any byte would produce this result. */

	diffs = 0;

	for (i = 0; i < blen / 2; i++)
	{

		u16 a = old_val >> (16 * i) , b = new_val >> (16 * i);

		if (a != b)
		{
			diffs++;
			ov = a;
			nv = b;
		}

	}

	/* If only one word differs and the values are within range, return 1. */

	if (diffs == 1)
	{

		if ((u16) (ov - nv) <= ARITH_MAX || (u16) (nv - ov) <= ARITH_MAX)
			return 1;

		ov = SWAP16(ov);
		nv = SWAP16(nv);

		if ((u16) (ov - nv) <= ARITH_MAX || (u16) (nv - ov) <= ARITH_MAX)
			return 1;

	}

	/* Finally, let's do the same thing for dwords. */

	if (blen == 4)
	{

		if ((u32) (old_val - new_val) <= ARITH_MAX
				|| (u32) (new_val - old_val) <= ARITH_MAX)
			return 1;

		new_val = SWAP32(new_val);
		old_val = SWAP32(old_val);

		if ((u32) (old_val - new_val) <= ARITH_MAX
				|| (u32) (new_val - old_val) <= ARITH_MAX)
			return 1;

	}

	return 0;

}

/* Last but not least, a similar helper to see if insertion of an 
 interesting integer is redundant given the insertions done for
 shorter blen. The last param (check_le) is set if the caller
 already executed LE insertion for current blen and wants to see
 if BE variant passed in new_val is unique. */

static u8 could_be_interest(u32 old_val, u32 new_val, u8 blen, u8 check_le)
{

	u32 i , j;

	if (old_val == new_val)
		return 1;

	/* See if one-byte insertions from interesting_8 over old_val could
	 produce new_val. */

	for (i = 0; i < blen; i++)
	{

		for (j = 0; j < sizeof(interesting_8); j++)
		{

			u32 tval = (old_val & ~(0xff << (i * 8)))
					| (((u8) interesting_8 [ j ]) << (i * 8));

			if (new_val == tval)
				return 1;

		}

	}

	/* Bail out unless we're also asked to examine two-byte LE insertions
	 as a preparation for BE attempts. */

	if (blen == 2 && !check_le)
		return 0;

	/* See if two-byte insertions over old_val could give us new_val. */

	for (i = 0; i < blen - 1; i++)
	{

		for (j = 0; j < sizeof(interesting_16) / 2; j++)
		{

			u32 tval = (old_val & ~(0xffff << (i * 8)))
					| (((u16) interesting_16 [ j ]) << (i * 8));

			if (new_val == tval)
				return 1;

			/* Continue here only if blen > 2. */

			if (blen > 2)
			{

				tval = (old_val & ~(0xffff << (i * 8)))
						| (SWAP16(interesting_16[j]) << (i * 8));

				if (new_val == tval)
					return 1;

			}

		}

	}

	if (blen == 4 && check_le)
	{

		/* See if four-byte insertions could produce the same result
		 (LE only). */

		for (j = 0; j < sizeof(interesting_32) / 4; j++)
			if (new_val == (u32) interesting_32 [ j ])
				return 1;

	}

	return 0;

}

/* Take the current entry from the queue, fuzz it for a while. This
 function is a tad too long... returns 0 if fuzzed successfully, 1 if
 skipped or bailed out. */

static u8 fuzz_one(char** argv)
{

	s32 len , fd , temp_len , i , j;
	u8 *in_buf , *out_buf , *orig_in , *ex_tmp , *eff_map = 0;
	u64 havoc_queued , orig_hit_cnt , new_hit_cnt;
	u32 splice_cycle = 0 , perf_score = 100 , orig_perf , prev_cksum , eff_cnt =1;

	u8 ret_val = 1;

	u8 a_collect [ MAX_AUTO_EXTRA ];
	u32 a_len = 0;

#ifdef XIAOSA
	u8 *tmpy = "";
	s32 fdy;
#endif

#ifdef IGNORE_FINDS

	/* In IGNORE_FINDS mode, skip any entries that weren't in the
	 initial data set. */

	if (queue_cur->depth > 1) return 1;

#else

	if (pending_favored)
	{ //pending_favored表示待测试的测试用例数量,是约简后的数量,第二轮之后不判断,除非有新的测试用例

		/* If we have any favored, non-fuzzed new arrivals in the queue,
		 possibly skip to them at the expense of already-fuzzed or non-favored
		 cases. */

		if ((queue_cur->was_fuzzed || !queue_cur->favored)
				&& UR(100) < SKIP_TO_NEW_PROB)
			return 1;

	}
	else if (!dumb_mode && !queue_cur->favored && queued_paths > 10)
	{

		/* Otherwise, still possibly skip non-favored cases, albeit less often.
		 The odds of skipping stuff are higher for already-fuzzed inputs and
		 lower for never-fuzzed entries. */

		if (queue_cycle > 1 && !queue_cur->was_fuzzed)
		{

			if (UR(100) < SKIP_NFAV_NEW_PROB)
				return 1;

		}
		else
		{

			if (UR(100) < SKIP_NFAV_OLD_PROB)
				return 1;

		}

	}

#endif /* ^IGNORE_FINDS */

	if (not_on_tty)
		ACTF("Fuzzing test case #%u (%u total)...",current_entry,queued_paths);

	/* Map the test case into memory. */

	fd = open(queue_cur->fname,O_RDONLY); //output/queue下

	if (fd < 0)
		PFATAL("Unable to open '%s'",queue_cur->fname);

	len = queue_cur->len;

	orig_in = in_buf = mmap(0,len,PROT_READ | PROT_WRITE,MAP_PRIVATE,fd,0);

	if (orig_in == MAP_FAILED)
		PFATAL("Unable to mmap '%s'",queue_cur->fname);

	close(fd);

#ifdef XIAOSA
	if (queue_cur->has_in_trace_plot == 0)
	{
		//open the trace_plot file
		tmpy = alloc_printf("%s/test_add.plot",out_dir);
		fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
		if (fdy < 0)
			PFATAL("Unable to create '%s'",tmpy);
		ck_free(tmpy);
		// current test case is executed
		tmpy = alloc_printf("	%u[shape=record];\n",queue_cur->self_id); //每次运行的测试用例都记录,但是会被多次记录
		ck_write(fdy,tmpy,strlen(tmpy),"test_add.plot");
		ck_free(tmpy);
		close(fdy);
		queue_cur->has_in_trace_plot = 1; //表示已经记录到trace_plot里了

	}

#endif

	/* We could mmap() out_buf as MAP_PRIVATE, but we end up clobbering every
	 single byte anyway, so it wouldn't give us any performance or memory usage
	 benefits. */

	out_buf = ck_alloc_nozero(len);

	subseq_hangs = 0;

	cur_depth = queue_cur->depth;

	/*******************************************
	 * CALIBRATION (only if failed earlier on) *  //判断之前的calibration是否成功
	 *******************************************/

	if (queue_cur->cal_failed)
	{ //之前calibration过之后,设置了cal_failed为0 ,即表示可以测试

		u8 res = FAULT_HANG;

		if (queue_cur->cal_failed < CAL_CHANCES)
		{

			res = calibrate_case(argv,queue_cur,in_buf,queue_cycle - 1,0);

			if (res == FAULT_ERROR)
				FATAL("Unable to execute target application");

		}

		if (stop_soon || res != crash_mode)
		{
			cur_skipped_paths++;
			goto abandon_entry;
		}

	}

	/************
	 * TRIMMING *
	 ************/
#if 1
	if (!dumb_mode && !queue_cur->trim_done)
	{ //插桩模式,且测试用例没有trim过

		u8 res = trim_case(argv,queue_cur,in_buf); //argv是启动qemu的命令

		if (res == FAULT_ERROR)
			FATAL("Unable to execute target application");

		if (stop_soon)
		{
			cur_skipped_paths++;
			goto abandon_entry;
		}

		/* Don't retry trimming, even if it failed. */

		queue_cur->trim_done = 1;

		if (len != queue_cur->len)
			len = queue_cur->len; //改变长度了

	}

	memcpy(out_buf,in_buf,len); //in_buf指向的值赋值给out_buf指向的值 即将测试用例内容赋值给out_buf
#endif
	/*********************
	 * PERFORMANCE SCORE *
	 *********************/

	orig_perf = perf_score = calculate_score(queue_cur); //打分的吧,没看

	/* Skip right away if -d is given, if we have done deterministic fuzzing on
	 this entry ourselves (was_fuzzed), or if it has gone through deterministic
	 testing in earlier, resumed runs (passed_det). */

	if (skip_deterministic || queue_cur->was_fuzzed || queue_cur->passed_det)
		goto havoc_stage; //三种情况下,跳过确定性阶段的变异fuzz

	/*********************************************
	 * SIMPLE BITFLIP (+dictionary construction) *
	 *********************************************/
	//依次对每一位取反,从最高位开始 这个思想和按位记录执行的操作方法一样
#define FLIP_BIT(_ar, _b) do { \
    u8* _arf = (u8*)(_ar); \
    u32 _bf = (_b); \
    _arf[(_bf) >> 3] ^= (128 >> ((_bf) & 7)); \
  } while (0)

	/* Single walking bit. */

	stage_short = "flip1";
	stage_max = len << 3; //测试用例长度*8 按bit变换 次数和测试用例长度一样
	stage_name = "bitflip 1/1";

	stage_val_type = STAGE_VAL_NONE;

	orig_hit_cnt = queued_paths + unique_crashes;

	prev_cksum = queue_cur->exec_cksum;

	for (stage_cur = 0; stage_cur < stage_max; stage_cur++)
	{

		stage_cur_byte = stage_cur >> 3;

		FLIP_BIT(out_buf,stage_cur); //对out_buf中的内容做了操作,根据stage_cur有不同的更改

		if (common_fuzz_stuff(argv,out_buf,len))
			goto abandon_entry;

		FLIP_BIT(out_buf,stage_cur); //对out_buf中的内容做了操作 恢复成原来

		/* While flipping the least significant bit in every byte, pull of an extra
		 trick to detect possible syntax tokens. In essence, the idea is that if
		 you have a binary blob like this:

		 xxxxxxxxIHDRxxxxxxxx

		 ...and changing the leading and trailing bytes causes variable or no
		 changes in program flow, but touching any character in the "IHDR" string
		 always produces the same, distinctive path, it's highly likely that
		 "IHDR" is an atomically-checked magic value of special significance to
		 the fuzzed format.

		 We do this here, rather than as a separate stage, because it's a nice
		 way to keep the operation approximately "free" (i.e., no extra execs).

		 Empirically, performing the check when flipping the least significant bit
		 is advantageous, compared to doing it at the time of more disruptive
		 changes, where the program flow may be affected in more violent ways.

		 The caveat is that we won't generate dictionaries in the -d mode or -S
		 mode - but that's probably a fair trade-off.

		 This won't work particularly well with paths that exhibit variable
		 behavior, but fails gracefully, so we'll carry out the checks anyway.

		 */

		if (!dumb_mode && (stage_cur & 7) == 7)
		{ //每进入一下, 处理字典方面的内容,待看

			u32 cksum = hash32(trace_bits,MAP_SIZE,HASH_CONST); //计算最新的哈希值

			if (stage_cur == stage_max - 1 && cksum == prev_cksum)
			{

				/* If at end of file and we are still collecting a string, grab the
				 final character and force output. */

				if (a_len < MAX_AUTO_EXTRA)
					a_collect [ a_len ] = out_buf [ stage_cur >> 3 ];
				a_len++;

				if (a_len >= MIN_AUTO_EXTRA && a_len <= MAX_AUTO_EXTRA)
					maybe_add_auto(a_collect,a_len);

			}
			else if (cksum != prev_cksum)
			{

				/* Otherwise, if the checksum has changed, see if we have something
				 worthwhile queued up, and collect that if the answer is yes. */

				if (a_len >= MIN_AUTO_EXTRA && a_len <= MAX_AUTO_EXTRA)
					maybe_add_auto(a_collect,a_len); //字典方面的内容

				a_len = 0;
				prev_cksum = cksum;

			}

			/* Continue collecting string, but only if the bit flip actually made
			 any difference - we don't want no-op tokens. */

			if (cksum != queue_cur->exec_cksum)
			{

				if (a_len < MAX_AUTO_EXTRA)
					a_collect [ a_len ] = out_buf [ stage_cur >> 3 ];
				a_len++;

			}

		}

	}

	new_hit_cnt = queued_paths + unique_crashes; //难道是执行的路径的某个信息

	stage_finds [ STAGE_FLIP1 ] += new_hit_cnt - orig_hit_cnt; //可能是某个stage下新增加的测试用例数量
	stage_cycles [ STAGE_FLIP1 ] += stage_max;

	if (queue_cur->passed_det)
		goto havoc_stage;

	/* Two walking bits. */

	stage_name = "bitflip 2/1";
	stage_short = "flip2";
	stage_max = (len << 3) - 1; //循环次数

	orig_hit_cnt = new_hit_cnt;

	for (stage_cur = 0; stage_cur < stage_max; stage_cur++)
	{

		stage_cur_byte = stage_cur >> 3;

		FLIP_BIT(out_buf,stage_cur);
		FLIP_BIT(out_buf,stage_cur + 1); //每次变化两个字节

		if (common_fuzz_stuff(argv,out_buf,len))
			goto abandon_entry;

		FLIP_BIT(out_buf,stage_cur);
		FLIP_BIT(out_buf,stage_cur + 1);

	}

	new_hit_cnt = queued_paths + unique_crashes; //

	stage_finds [ STAGE_FLIP2 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_FLIP2 ] += stage_max;

	/* Four walking bits. */

	stage_name = "bitflip 4/1";
	stage_short = "flip4";
	stage_max = (len << 3) - 3;

	orig_hit_cnt = new_hit_cnt;

	for (stage_cur = 0; stage_cur < stage_max; stage_cur++)
	{

		stage_cur_byte = stage_cur >> 3;

		FLIP_BIT(out_buf,stage_cur);
		FLIP_BIT(out_buf,stage_cur + 1);
		FLIP_BIT(out_buf,stage_cur + 2);
		FLIP_BIT(out_buf,stage_cur + 3);

		if (common_fuzz_stuff(argv,out_buf,len))
			goto abandon_entry;

		FLIP_BIT(out_buf,stage_cur);
		FLIP_BIT(out_buf,stage_cur + 1);
		FLIP_BIT(out_buf,stage_cur + 2);
		FLIP_BIT(out_buf,stage_cur + 3);

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_FLIP4 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_FLIP4 ] += stage_max;

	/* Effector map setup. These macros calculate:

	 EFF_APOS      - position of a particular file offset in the map.
	 EFF_ALEN      - length of an map with a particular number of bytes.
	 EFF_SPAN_ALEN - map span for a sequence of bytes.

	 */

#define EFF_APOS(_p)          ((_p) >> EFF_MAP_SCALE2)  //除8 block的index
#define EFF_REM(_x)           ((_x) & ((1 << EFF_MAP_SCALE2) - 1))  //,后面一个值是7,即取_x低3位
#define EFF_ALEN(_l)          (EFF_APOS(_l) + !!EFF_REM(_l))  //两次求反变0 1  长度/8+低三位是否有值,不是8的整数,再加1
#define EFF_SPAN_ALEN(_p, _l) (EFF_APOS((_p) + (_l) - 1) - EFF_APOS(_p) + 1) //这个宏在字典中才用到

	/* Initialize effector map for the next step (see comments below). Always
	 flag first and last byte as doing something. */

	eff_map = ck_alloc(EFF_ALEN(len)); //给指针分配大小
	eff_map [ 0 ] = 1;

	if (EFF_APOS(len - 1) != 0)
	{  //如果数组长度大于1
		eff_map [ EFF_APOS(len - 1) ] = 1;  //最后一个字节赋值1  认为最前和最后是有影响的
		eff_cnt++; //表示eff_map中1的个数
	}

	/* Walking byte. */

	stage_name = "bitflip 8/8";
	stage_short = "flip8";
	stage_max = len; //测试用例的长度,字节数量

	orig_hit_cnt = new_hit_cnt;

	for (stage_cur = 0; stage_cur < stage_max; stage_cur++)
	{

		stage_cur_byte = stage_cur;

		out_buf [ stage_cur ] ^= 0xFF; //取反 对某个字节取反

		if (common_fuzz_stuff(argv,out_buf,len))
			goto abandon_entry;

		/* We also use this stage to pull off a simple trick: we identify
		 bytes that seem to have no effect on the current execution path
		 even when fully flipped - and we skip them during more expensive
		 deterministic stages, such as arithmetics or known ints. */
		//用来标记关键字段
		if (!eff_map [ EFF_APOS(stage_cur) ])
		{ //当eff_map指向的值为0的时候 每8个字节用一个字节的eff_map

			u32 cksum;

			/* If in dumb mode or if the file is very short, just flag everything
			 without wasting time on checksums. */

			if (!dumb_mode && len >= EFF_MIN_LEN)
				cksum = hash32(trace_bits,MAP_SIZE,HASH_CONST); //输入很长的时候,判断是否有影响
			else
				cksum = ~queue_cur->exec_cksum; //输入很短的时候,认为都有影响,不插桩的话,也只能认为所有字段都是关键的

			if (cksum != queue_cur->exec_cksum)
			{ //比较取反后和没有取反的执行轨迹
				eff_map [ EFF_APOS(stage_cur) ] = 1; //effe_map赋值为1,表示有影响
				eff_cnt++;
			}

		}

		out_buf [ stage_cur ] ^= 0xFF; //恢复

	}

	/* If the effector map is more than EFF_MAX_PERC dense, just flag the
	 whole thing as worth fuzzing, since we wouldn't be saving much time
	 anyway. */

	if (eff_cnt != EFF_ALEN(len) && eff_cnt * 100 / EFF_ALEN(len) > EFF_MAX_PERC)
	{ //计算影响的范围,以及影响范围的比例

		memset(eff_map,1,EFF_ALEN(len)); //如果影响超过90%,即认为全部用用

		blocks_eff_select += EFF_ALEN(len);

	}
	else
	{

		blocks_eff_select += eff_cnt; //受影响的block数量

	}

	blocks_eff_total += EFF_ALEN(len); //总共的block数量

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_FLIP8 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_FLIP8 ] += stage_max;

	/* Two walking bytes. */

	if (len < 2)
		goto skip_bitflip;

	stage_name = "bitflip 16/8";
	stage_short = "flip16";
	stage_cur = 0;
	stage_max = len - 1;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len - 1; i++)
	{

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ] && !eff_map [ EFF_APOS(i + 1) ])
		{
			stage_max--; //记录测试的次数
			continue;  //如果第i个字节和第i+1个字节所在的block中有一个不受影响,则跳过本次
		}

		stage_cur_byte = i;

		*(u16*) (out_buf + i) ^= 0xFFFF; //16位取反

		if (common_fuzz_stuff(argv,out_buf,len))
			goto abandon_entry;
		stage_cur++;

		*(u16*) (out_buf + i) ^= 0xFFFF;

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_FLIP16 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_FLIP16 ] += stage_max;  //记录测试的次数

	if (len < 4)
		goto skip_bitflip;
	//长度太短就不玩

	/* Four walking bytes. */

	stage_name = "bitflip 32/8";
	stage_short = "flip32";
	stage_cur = 0;
	stage_max = len - 3;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len - 3; i++)
	{

		/* Let's consult the effector map... */
		if (!eff_map [ EFF_APOS(i) ] && !eff_map [ EFF_APOS(i + 1) ]
				&& !eff_map [ EFF_APOS(i + 2) ] && !eff_map [ EFF_APOS(i + 3) ])
		{
			stage_max--;
			continue;
		}

		stage_cur_byte = i;

		*(u32*) (out_buf + i) ^= 0xFFFFFFFF; //32位取反

		if (common_fuzz_stuff(argv,out_buf,len))
			goto abandon_entry;
		stage_cur++;

		*(u32*) (out_buf + i) ^= 0xFFFFFFFF;

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_FLIP32 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_FLIP32 ] += stage_max;

	skip_bitflip:

	/**********************
	 * ARITHMETIC INC/DEC *
	 **********************/

	/* 8-bit arithmetics. */

	stage_name = "arith 8/8";
	stage_short = "arith8";
	stage_cur = 0;
	stage_max = 2 * len * ARITH_MAX;

	stage_val_type = STAGE_VAL_LE;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len; i++)
	{

		u8 orig = out_buf [ i ];  //这个不是指针

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ])
		{
			stage_max -= 2 * ARITH_MAX; //ARITH_MAX is 35 减少测试次数
			continue;
		}

		stage_cur_byte = i;

		for (j = 1; j <= ARITH_MAX; j++)
		{

			u8 r = orig ^ (orig + j); //orig不是指针,orig + j的值会溢出,不会大于256

			/* Do arithmetic operations only if the result couldn't be a product
			 of a bitflip. */

			if (!could_be_bitflip(r))
			{
				//没有在bitflip中出现过
				stage_cur_val = j;
				out_buf [ i ] = orig + j; //测试的是加j的内容

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			r = orig ^ (orig - j); //往后

			if (!could_be_bitflip(r))
			{

				stage_cur_val = -j;
				out_buf [ i ] = orig - j;

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			out_buf [ i ] = orig; //恢复

		}

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_ARITH8 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_ARITH8 ] += stage_max;

	/* 16-bit arithmetics, both endians. */

	if (len < 2)
		goto skip_arith;

	stage_name = "arith 16/8";
	stage_short = "arith16";
	stage_cur = 0;
	stage_max = 4 * (len - 1) * ARITH_MAX;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len - 1; i++)
	{

		u16 orig = *(u16*) (out_buf + i); //一次取了两个字节,步长是1个字节

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ] && !eff_map [ EFF_APOS(i + 1) ])
		{
			stage_max -= 4 * ARITH_MAX;
			continue;
		}

		stage_cur_byte = i;

		for (j = 1; j <= ARITH_MAX; j++)
		{

			u16 r1 = orig ^ (orig + j) , //值不会大于65536,,这两个字节之间有进位
			r2 = orig ^ (orig - j) , r3 = orig ^ SWAP16(SWAP16(orig) + j) , //swap宏是互换前8位和后8位,为了考虑大端和小端
					r4 = orig ^ SWAP16(SWAP16(orig) - j);

			/* Try little endian addition and subtraction first. Do it only
			 if the operation would affect more than one byte (hence the
			 & 0xff overflow checks) and if it couldn't be a product of
			 a bitflip. */

			stage_val_type = STAGE_VAL_LE;  //小端

			if ((orig & 0xff) + j > 0xff && !could_be_bitflip(r1))
			{ //必须要进位,否则和8bit的计算阶段一样了

				stage_cur_val = j;
				*(u16*) (out_buf + i) = orig + j;  //低8位的处理

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			if ((orig & 0xff) < j && !could_be_bitflip(r2))
			{  //必须退位

				stage_cur_val = -j;
				*(u16*) (out_buf + i) = orig - j;

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			/* Big endian comes next. Same deal. */

			stage_val_type = STAGE_VAL_BE; //大端

			if ((orig >> 8) + j > 0xff && !could_be_bitflip(r3))
			{

				stage_cur_val = j;
				*(u16*) (out_buf + i) = SWAP16(SWAP16(orig) + j);

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			if ((orig >> 8) < j && !could_be_bitflip(r4))
			{

				stage_cur_val = -j;
				*(u16*) (out_buf + i) = SWAP16(SWAP16(orig) - j);

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			*(u16*) (out_buf + i) = orig;

		}

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_ARITH16 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_ARITH16 ] += stage_max;

	/* 32-bit arithmetics, both endians. */

	if (len < 4)
		goto skip_arith;

	stage_name = "arith 32/8";
	stage_short = "arith32";
	stage_cur = 0;
	stage_max = 4 * (len - 3) * ARITH_MAX;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len - 3; i++)
	{

		u32 orig = *(u32*) (out_buf + i);

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ] && !eff_map [ EFF_APOS(i + 1) ]
				&& !eff_map [ EFF_APOS(i + 2) ] && !eff_map [ EFF_APOS(i + 3) ])
		{
			stage_max -= 4 * ARITH_MAX;
			continue;
		}

		stage_cur_byte = i;

		for (j = 1; j <= ARITH_MAX; j++)
		{

			u32 r1 = orig ^ (orig + j) , r2 = orig ^ (orig - j) , r3 = orig
					^ SWAP32(SWAP32(orig) + j) , r4 = orig
					^ SWAP32(SWAP32(orig) - j);

			/* Little endian first. Same deal as with 16-bit: we only want to
			 try if the operation would have effect on more than two bytes. */

			stage_val_type = STAGE_VAL_LE;

			if ((orig & 0xffff) + j > 0xffff && !could_be_bitflip(r1))
			{

				stage_cur_val = j;
				*(u32*) (out_buf + i) = orig + j;

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			if ((orig & 0xffff) < j && !could_be_bitflip(r2))
			{

				stage_cur_val = -j;
				*(u32*) (out_buf + i) = orig - j;

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			/* Big endian next. */

			stage_val_type = STAGE_VAL_BE;

			if ((SWAP32(orig) & 0xffff) + j > 0xffff && !could_be_bitflip(r3))
			{

				stage_cur_val = j;
				*(u32*) (out_buf + i) = SWAP32(SWAP32(orig) + j);

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			if ((SWAP32(orig) & 0xffff) < j && !could_be_bitflip(r4))
			{

				stage_cur_val = -j;
				*(u32*) (out_buf + i) = SWAP32(SWAP32(orig) - j);

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			*(u32*) (out_buf + i) = orig;

		}

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_ARITH32 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_ARITH32 ] += stage_max;

	skip_arith:

	/**********************
	 * INTERESTING VALUES *
	 **********************/

	stage_name = "interest 8/8";
	stage_short = "int8";
	stage_cur = 0;
	stage_max = len * sizeof(interesting_8);

	stage_val_type = STAGE_VAL_LE;

	orig_hit_cnt = new_hit_cnt;

	/* Setting 8-bit integers. */

	for (i = 0; i < len; i++)
	{

		u8 orig = out_buf [ i ];

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ])
		{
			stage_max -= sizeof(interesting_8);
			continue;
		}

		stage_cur_byte = i;

		for (j = 0; j < sizeof(interesting_8); j++)
		{

			/* Skip if the value could be a product of bitflips or arithmetics. */

			if (could_be_bitflip(orig ^ (u8) interesting_8 [ j ])
					|| could_be_arith(orig,(u8) interesting_8 [ j ],1))
			{
				stage_max--;
				continue;
			}

			stage_cur_val = interesting_8 [ j ];
			out_buf [ i ] = interesting_8 [ j ];

			if (common_fuzz_stuff(argv,out_buf,len))
				goto abandon_entry;

			out_buf [ i ] = orig;
			stage_cur++;

		}

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_INTEREST8 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_INTEREST8 ] += stage_max;

	/* Setting 16-bit integers, both endians. */

	if (len < 2)
		goto skip_interest;

	stage_name = "interest 16/8";
	stage_short = "int16";
	stage_cur = 0;
	stage_max = 2 * (len - 1) * (sizeof(interesting_16) >> 1); //每个interesting_16数组中每个是2个字节

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len - 1; i++)
	{

		u16 orig = *(u16*) (out_buf + i);

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ] && !eff_map [ EFF_APOS(i + 1) ])
		{
			stage_max -= sizeof(interesting_16);
			continue;
		}

		stage_cur_byte = i;

		for (j = 0; j < sizeof(interesting_16) / 2; j++)
		{

			stage_cur_val = interesting_16 [ j ];

			/* Skip if this could be a product of a bitflip, arithmetics,
			 or single-byte interesting value insertion. */

			if (!could_be_bitflip(orig ^ (u16) interesting_16 [ j ])
					&& !could_be_arith(orig,(u16) interesting_16 [ j ],2)
					&& !could_be_interest(orig,(u16) interesting_16 [ j ],2,0))
			{

				stage_val_type = STAGE_VAL_LE;

				*(u16*) (out_buf + i) = interesting_16 [ j ];

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			if ((u16) interesting_16 [ j ] != SWAP16(interesting_16 [ j ])
					&& !could_be_bitflip(orig ^ SWAP16(interesting_16 [ j ]))
					&& !could_be_arith(orig,SWAP16(interesting_16 [ j ]),2)
					&& !could_be_interest(orig,SWAP16(interesting_16 [ j ]),2,
							1))
			{

				stage_val_type = STAGE_VAL_BE;

				*(u16*) (out_buf + i) = SWAP16(interesting_16 [ j ]);
				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

		}

		*(u16*) (out_buf + i) = orig;

	}

	new_hit_cnt = queued_paths + unique_crashes; //新增加到几个测试用例

	stage_finds [ STAGE_INTEREST16 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_INTEREST16 ] += stage_max;

	if (len < 4)
		goto skip_interest;

	/* Setting 32-bit integers, both endians. */

	stage_name = "interest 32/8";
	stage_short = "int32";
	stage_cur = 0;
	stage_max = 2 * (len - 3) * (sizeof(interesting_32) >> 2); //数组中每个是4个字节

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len - 3; i++)
	{

		u32 orig = *(u32*) (out_buf + i);

		/* Let's consult the effector map... */

		if (!eff_map [ EFF_APOS(i) ] && !eff_map [ EFF_APOS(i + 1) ]
				&& !eff_map [ EFF_APOS(i + 2) ] && !eff_map [ EFF_APOS(i + 3) ])
		{
			stage_max -= sizeof(interesting_32) >> 1;
			continue;
		}

		stage_cur_byte = i;

		for (j = 0; j < sizeof(interesting_32) / 4; j++)
		{

			stage_cur_val = interesting_32 [ j ];

			/* Skip if this could be a product of a bitflip, arithmetics,
			 or word interesting value insertion. */

			if (!could_be_bitflip(orig ^ (u32) interesting_32 [ j ])
					&& !could_be_arith(orig,interesting_32 [ j ],4)
					&& !could_be_interest(orig,interesting_32 [ j ],4,0))
			{

				stage_val_type = STAGE_VAL_LE;

				*(u32*) (out_buf + i) = interesting_32 [ j ];

				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

			if ((u32) interesting_32 [ j ] != SWAP32(interesting_32 [ j ])
					&& !could_be_bitflip(orig ^ SWAP32(interesting_32 [ j ]))
					&& !could_be_arith(orig,SWAP32(interesting_32 [ j ]),4)
					&& !could_be_interest(orig,SWAP32(interesting_32 [ j ]),4,
							1))
			{

				stage_val_type = STAGE_VAL_BE;

				*(u32*) (out_buf + i) = SWAP32(interesting_32 [ j ]);
				if (common_fuzz_stuff(argv,out_buf,len))
					goto abandon_entry;
				stage_cur++;

			}
			else
				stage_max--;

		}

		*(u32*) (out_buf + i) = orig;

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_INTEREST32 ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_INTEREST32 ] += stage_max;

	skip_interest:

	/********************
	 * DICTIONARY STUFF *
	 ********************/

	if (!extras_cnt)
		goto skip_user_extras;

	/* Overwrite with user-supplied extras. */

	stage_name = "user extras (over)";
	stage_short = "ext_UO";
	stage_cur = 0;
	stage_max = extras_cnt * len;

	stage_val_type = STAGE_VAL_NONE;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len; i++)
	{

		u32 last_len = 0;

		stage_cur_byte = i;

		/* Extras are sorted by size, from smallest to largest. This means
		 that we don't have to worry about restoring the buffer in
		 between writes at a particular offset determined by the outer
		 loop. */

		for (j = 0; j < extras_cnt; j++)
		{

			/* Skip extras probabilistically if extras_cnt > MAX_DET_EXTRAS. Also
			 skip them if there's no room to insert the payload, if the token
			 is redundant, or if its entire span has no bytes set in the effector
			 map. */

			if ((extras_cnt > MAX_DET_EXTRAS && UR(extras_cnt) >= MAX_DET_EXTRAS)
					|| extras [ j ].len > len - i
					|| !memcmp(extras [ j ].data,out_buf + i,extras [ j ].len)
					|| !memchr(eff_map + EFF_APOS(i),1,
							EFF_SPAN_ALEN(i,extras [ j ].len)))
			{

				stage_max--;
				continue;

			}

			last_len = extras [ j ].len;
			memcpy(out_buf + i,extras [ j ].data,last_len);

			if (common_fuzz_stuff(argv,out_buf,len))
				goto abandon_entry;

			stage_cur++;

		}

		/* Restore all the clobbered memory. */
		memcpy(out_buf + i,in_buf + i,last_len);

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_EXTRAS_UO ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_EXTRAS_UO ] += stage_max;

	/* Insertion of user-supplied extras. */

	stage_name = "user extras (insert)";
	stage_short = "ext_UI";
	stage_cur = 0;
	stage_max = extras_cnt * len;

	orig_hit_cnt = new_hit_cnt;

	ex_tmp = ck_alloc(len + MAX_DICT_FILE);

	for (i = 0; i < len; i++)
	{

		stage_cur_byte = i;

		for (j = 0; j < extras_cnt; j++)
		{

			/* Insert token */
			memcpy(ex_tmp + i,extras [ j ].data,extras [ j ].len);

			/* Copy tail */
			memcpy(ex_tmp + i + extras [ j ].len,out_buf + i,len - i);

			if (common_fuzz_stuff(argv,ex_tmp,len + extras [ j ].len))
			{
				ck_free(ex_tmp);
				goto abandon_entry;
			}

			stage_cur++;

		}

		/* Copy head */
		ex_tmp [ i ] = out_buf [ i ];

	}

	ck_free(ex_tmp);

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_EXTRAS_UI ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_EXTRAS_UI ] += stage_max;

	skip_user_extras:

	if (!a_extras_cnt)
		goto skip_extras;

	stage_name = "auto extras (over)";
	stage_short = "ext_AO";
	stage_cur = 0;
	stage_max = MIN(a_extras_cnt, USE_AUTO_EXTRAS) * len;

	stage_val_type = STAGE_VAL_NONE;

	orig_hit_cnt = new_hit_cnt;

	for (i = 0; i < len; i++)
	{

		u32 last_len = 0;

		stage_cur_byte = i;

		for (j = 0; j < MIN(a_extras_cnt,USE_AUTO_EXTRAS); j++)
		{

			/* See the comment in the earlier code; extras are sorted by size. */

			if (a_extras [ j ].len > len - i
					|| !memcmp(a_extras [ j ].data,out_buf + i,
							a_extras [ j ].len)
					|| !memchr(eff_map + EFF_APOS(i),1,
							EFF_SPAN_ALEN(i,a_extras [ j ].len)))
			{

				stage_max--;
				continue;

			}

			last_len = a_extras [ j ].len;
			memcpy(out_buf + i,a_extras [ j ].data,last_len);

			if (common_fuzz_stuff(argv,out_buf,len))
				goto abandon_entry;

			stage_cur++;

		}

		/* Restore all the clobbered memory. */
		memcpy(out_buf + i,in_buf + i,last_len);

	}

	new_hit_cnt = queued_paths + unique_crashes;

	stage_finds [ STAGE_EXTRAS_AO ] += new_hit_cnt - orig_hit_cnt;
	stage_cycles [ STAGE_EXTRAS_AO ] += stage_max;

	skip_extras:

	/* If we made this to here without jumping to havoc_stage or abandon_entry,
	 we're properly done with deterministic steps and can mark it as such
	 in the .state/ directory. */

	if (!queue_cur->passed_det)
		mark_as_det_done(queue_cur); //避免重复进行确定性变异

	/****************
	 * RANDOM HAVOC *
	 ****************/

havoc_stage:

	stage_cur_byte = -1; //不知道偏移量了

	/* The havoc stage mutation code is also invoked when splicing files; if the
	 splice_cycle variable is set, generate different descriptions and such. */

	if (!splice_cycle)
	{

		stage_name = "havoc";
		stage_short = "havoc";
		stage_max = HAVOC_CYCLES * perf_score / havoc_div / 100;
					//即对HAVOC_CYCLES乘以一个系数,HAVOC_CYCLES是一个基本数
	}
	else
	{

		static u8 tmp [ 32 ];

		perf_score = orig_perf;

		sprintf(tmp,"splice %u",splice_cycle);
		stage_name = tmp;
		stage_short = "splice";
		stage_max = SPLICE_HAVOC * perf_score / havoc_div / 100; //循环次数计算

	}

	if (stage_max < HAVOC_MIN) //为了保证最小次数
		stage_max = HAVOC_MIN;

	temp_len = len;

	orig_hit_cnt = queued_paths + unique_crashes;

	havoc_queued = queued_paths;

	/* We essentially just do several thousand runs (depending on perf_score)
	 where we take the input file and make random stacked tweaks. */
	//stage_max 最小为HAVOC_MIN次,这里为10次
	for (stage_cur = 0; stage_cur < stage_max; stage_cur++)
	{

		u32 use_stacking = 1 << (1 + UR(HAVOC_STACK_POW2)); //随机设置操作次数,1到256之间随机

		stage_cur_val = use_stacking; //记录采取的操作循环次数

		for (i = 0; i < use_stacking; i++)
		{ //随机选择

			switch (UR(15 + ((extras_cnt + a_extras_cnt) ? 2 : 0)))
			{

				case 0 :

					/* Flip a single bit somewhere. Spooky! */

					FLIP_BIT(out_buf,UR(temp_len << 3));
					break;

				case 1 :

					/* Set byte to interesting value. */

					out_buf [ UR(temp_len) ] = interesting_8 [ UR(
							sizeof(interesting_8)) ];
					break;

				case 2 :

					/* Set word to interesting value, randomly choosing endian. */

					if (temp_len < 2)
						break;

					if (UR(2))
					{

						*(u16*) (out_buf + UR(temp_len - 1)) =
								interesting_16 [ UR(sizeof(interesting_16) >> 1) ];

					}
					else
					{

						*(u16*) (out_buf + UR(temp_len - 1)) =
								SWAP16(
										interesting_16 [ UR(
												sizeof(interesting_16) >> 1) ]);

					}

					break;

				case 3 :

					/* Set dword to interesting value, randomly choosing endian. */

					if (temp_len < 4)
						break;

					if (UR(2))
					{

						*(u32*) (out_buf + UR(temp_len - 3)) =
								interesting_32 [ UR(sizeof(interesting_32) >> 2) ];

					}
					else
					{

						*(u32*) (out_buf + UR(temp_len - 3)) =
								SWAP32(
										interesting_32 [ UR(
												sizeof(interesting_32) >> 2) ]);

					}

					break;

				case 4 :

					/* Randomly subtract from byte. */

					out_buf [ UR(temp_len) ] -= 1 + UR(ARITH_MAX);
					break;

				case 5 :

					/* Randomly add to byte. */

					out_buf [ UR(temp_len) ] += 1 + UR(ARITH_MAX);
					break;

				case 6 :

					/* Randomly subtract from word, random endian. */

					if (temp_len < 2)
						break;

					if (UR(2))
					{

						u32 pos = UR(temp_len - 1);

						*(u16*) (out_buf + pos) -= 1 + UR(ARITH_MAX);

					}
					else
					{

						u32 pos = UR(temp_len - 1);
						u16 num = 1 + UR(ARITH_MAX);

						*(u16*) (out_buf + pos) = SWAP16(
								SWAP16(*(u16*)(out_buf + pos)) - num);

					}

					break;

				case 7 :

					/* Randomly add to word, random endian. */

					if (temp_len < 2)
						break;

					if (UR(2))
					{

						u32 pos = UR(temp_len - 1);

						*(u16*) (out_buf + pos) += 1 + UR(ARITH_MAX);

					}
					else
					{

						u32 pos = UR(temp_len - 1);
						u16 num = 1 + UR(ARITH_MAX);

						*(u16*) (out_buf + pos) = SWAP16(
								SWAP16(*(u16*)(out_buf + pos)) + num);

					}

					break;

				case 8 :

					/* Randomly subtract from dword, random endian. */

					if (temp_len < 4)
						break;

					if (UR(2))
					{

						u32 pos = UR(temp_len - 3);

						*(u32*) (out_buf + pos) -= 1 + UR(ARITH_MAX);

					}
					else
					{

						u32 pos = UR(temp_len - 3);
						u32 num = 1 + UR(ARITH_MAX);

						*(u32*) (out_buf + pos) = SWAP32(
								SWAP32(*(u32*)(out_buf + pos)) - num);

					}

					break;

				case 9 :

					/* Randomly add to dword, random endian. */

					if (temp_len < 4)
						break;

					if (UR(2))
					{

						u32 pos = UR(temp_len - 3);

						*(u32*) (out_buf + pos) += 1 + UR(ARITH_MAX);

					}
					else
					{

						u32 pos = UR(temp_len - 3);
						u32 num = 1 + UR(ARITH_MAX);

						*(u32*) (out_buf + pos) = SWAP32(
								SWAP32(*(u32*)(out_buf + pos)) + num);

					}

					break;

				case 10 :

					/* Just set a random byte to a random value. Because,
					 why not. We use XOR with 1-255 to eliminate the
					 possibility of a no-op. */

					out_buf [ UR(temp_len) ] ^= 1 + UR(255);
					break;

				case 11 ... 12 :
				{

					/* Delete bytes. We're making this a bit more likely
					 than insertion (the next option) in hopes of keeping
					 files reasonably small. */

					u32 del_from , del_len;

					if (temp_len < 2)
						break;

					/* Don't delete too much. */

					del_len = choose_block_len(temp_len - 1);

					del_from = UR(temp_len - del_len + 1);

					memmove(out_buf + del_from,out_buf + del_from + del_len,
							temp_len - del_from - del_len);

					temp_len -= del_len;

					break;

				}

				case 13 :

					if (temp_len + HAVOC_BLK_LARGE < MAX_FILE)
					{

						/* Clone bytes (75%) or insert a block of constant bytes (25%). */

						u32 clone_from , clone_to , clone_len;
						u8* new_buf;

						clone_len = choose_block_len(temp_len);

						clone_from = UR(temp_len - clone_len + 1);
						clone_to = UR(temp_len);

						new_buf = ck_alloc_nozero(temp_len + clone_len);

						/* Head */

						memcpy(new_buf,out_buf,clone_to);

						/* Inserted part */

						if (UR(4))
							memcpy(new_buf + clone_to,out_buf + clone_from,
									clone_len);
						else
							memset(new_buf + clone_to,UR(256),clone_len);

						/* Tail */
						memcpy(new_buf + clone_to + clone_len,
								out_buf + clone_to,temp_len - clone_to);

						ck_free(out_buf);
						out_buf = new_buf;
						temp_len += clone_len;

					}

					break;

				case 14 :
				{

					/* Overwrite bytes with a randomly selected chunk (75%) or fixed
					 bytes (25%). */

					u32 copy_from , copy_to , copy_len;

					if (temp_len < 2)
						break;

					copy_len = choose_block_len(temp_len - 1);

					copy_from = UR(temp_len - copy_len + 1);
					copy_to = UR(temp_len - copy_len + 1);

					if (UR(4))
					{

						if (copy_from != copy_to)
							memmove(out_buf + copy_to,out_buf + copy_from,
									copy_len);

					}
					else
						memset(out_buf + copy_to,UR(256),copy_len);

					break;

				}

					/* Values 16 and 17 can be selected only if there are any extras
					 present in the dictionaries. */

				case 16 :
				{

					/* Overwrite bytes with an extra. */

					if (!extras_cnt || (a_extras_cnt && UR(2)))
					{

						/* No user-specified extras or odds in our favor. Let's use an
						 auto-detected one. */

						u32 use_extra = UR(a_extras_cnt);
						u32 extra_len = a_extras [ use_extra ].len;
						u32 insert_at;

						if (extra_len > temp_len)
							break;

						insert_at = UR(temp_len - extra_len + 1);
						memcpy(out_buf + insert_at,a_extras [ use_extra ].data,
								extra_len);

					}
					else
					{

						/* No auto extras or odds in our favor. Use the dictionary. */

						u32 use_extra = UR(extras_cnt);
						u32 extra_len = extras [ use_extra ].len;
						u32 insert_at;

						if (extra_len > temp_len)
							break;

						insert_at = UR(temp_len - extra_len + 1);
						memcpy(out_buf + insert_at,extras [ use_extra ].data,
								extra_len);

					}

					break;

				}

				case 17 :
				{

					u32 use_extra , extra_len , insert_at = UR(temp_len);
					u8* new_buf;

					/* Insert an extra. Do the same dice-rolling stuff as for the
					 previous case. */

					if (!extras_cnt || (a_extras_cnt && UR(2)))
					{

						use_extra = UR(a_extras_cnt);
						extra_len = a_extras [ use_extra ].len;

						if (temp_len + extra_len >= MAX_FILE)
							break;

						new_buf = ck_alloc_nozero(temp_len + extra_len);

						/* Head */
						memcpy(new_buf,out_buf,insert_at);

						/* Inserted part */
						memcpy(new_buf + insert_at,a_extras [ use_extra ].data,
								extra_len);

					}
					else
					{

						use_extra = UR(extras_cnt);
						extra_len = extras [ use_extra ].len;

						if (temp_len + extra_len >= MAX_FILE)
							break;

						new_buf = ck_alloc_nozero(temp_len + extra_len);

						/* Head */
						memcpy(new_buf,out_buf,insert_at);

						/* Inserted part */
						memcpy(new_buf + insert_at,extras [ use_extra ].data,
								extra_len);

					}

					/* Tail */
					memcpy(new_buf + insert_at + extra_len,out_buf + insert_at,
							temp_len - insert_at);

					ck_free(out_buf);
					out_buf = new_buf;
					temp_len += extra_len;

					break;

				}

			}

		}

		if (common_fuzz_stuff(argv,out_buf,temp_len))
			goto abandon_entry; //如果结束或者被挂起,就不再跑了

		/* out_buf might have been mangled a bit, so let's restore it to its
		 original size and shape. */
		//恢复成in_buf,是queue中的值
		if (temp_len < len)
			out_buf = ck_realloc(out_buf,len); //判断是否改变长度
		temp_len = len;
		memcpy(out_buf,in_buf,len);

		/* If we're finding new stuff, let's run for a bit longer, limits
		 permitting. */
		//如果发现了新的路径,就多跑一会
		if (queued_paths != havoc_queued)
		{

			if (perf_score <= HAVOC_MAX_MULT * 100)
			{
				stage_max *= 2;
				perf_score *= 2;
			}

			havoc_queued = queued_paths;

		}

	}

	new_hit_cnt = queued_paths + unique_crashes;

	if (!splice_cycle)
	{
		stage_finds [ STAGE_HAVOC ] += new_hit_cnt - orig_hit_cnt;
		stage_cycles [ STAGE_HAVOC ] += stage_max;
	}
	else
	{
		stage_finds [ STAGE_SPLICE ] += new_hit_cnt - orig_hit_cnt;
		stage_cycles [ STAGE_SPLICE ] += stage_max;
	}

#ifndef IGNORE_FINDS

	/************
	 * SPLICING *
	 ************/

	/* This is a last-resort strategy triggered by a full round with no findings.
	 It takes the current input file, randomly selects another input, and
	 splices them together at some offset, then relies on the havoc
	 code to mutate that blob. */

	retry_splicing:

	if (use_splicing && splice_cycle++ < SPLICE_CYCLES && queued_paths > 1
			&& queue_cur->len > 1)
	{

		struct queue_entry* target;
		u32 tid , split_at;
		u8* new_buf;
		s32 f_diff , l_diff;

		/* First of all, if we've modified in_buf for havoc, let's clean that
		 up... */

		if (in_buf != orig_in)
		{
			ck_free(in_buf);
			in_buf = orig_in;
			len = queue_cur->len;
		}

		/* Pick a random queue entry and seek to it. Don't splice with yourself. */

		do
		{
			tid = UR(queued_paths);
		} while (tid == current_entry);

		splicing_with = tid;  //表示选择的其他测试用例的id
		target = queue;

		while (tid >= 100)
		{
			target = target->next_100;
			tid -= 100;
		} //往前退100
		while (tid--)
			target = target->next;

		/* Make sure that the target has a reasonable length. */

		while (target && (target->len < 2 || target == queue_cur))
		{
			target = target->next;
			splicing_with++;
		}

		if (!target)
			goto retry_splicing;

		/* Read the testcase into a new buffer. */

		fd = open(target->fname,O_RDONLY);

		if (fd < 0)
			PFATAL("Unable to open '%s'",target->fname);

		new_buf = ck_alloc_nozero(target->len);

		ck_read(fd,new_buf,target->len,target->fname);

		close(fd);

		/* Find a suitable splicing location, somewhere between the first and
		 the last differing byte. Bail out if the difference is just a single
		 byte or so. */

		locate_diffs(in_buf,new_buf,MIN(len,target->len),&f_diff,&l_diff);

		if (f_diff < 0 || l_diff < 2 || f_diff == l_diff)
		{
			ck_free(new_buf);
			goto retry_splicing;
		}

		/* Split somewhere between the first and last differing byte. */

		split_at = f_diff + UR(l_diff - f_diff);

		/* Do the thing. */

		len = target->len;
		memcpy(new_buf,in_buf,split_at);
		in_buf = new_buf;

		ck_free(out_buf);
		out_buf = ck_alloc_nozero(len);
		memcpy(out_buf,in_buf,len);

		goto havoc_stage;

	}

#endif /* !IGNORE_FINDS */

	ret_val = 0;

	abandon_entry:

	splicing_with = -1;

	/* Update pending_not_fuzzed count if we made it through the calibration
	 cycle and have not seen this entry before. */

	if (!stop_soon && !queue_cur->cal_failed && !queue_cur->was_fuzzed)
	{
		queue_cur->was_fuzzed = 1;
		pending_not_fuzzed--;
		if (queue_cur->favored)
			pending_favored--; //跑完一个之后就减1
	}

	munmap(orig_in,queue_cur->len); //释放

	if (in_buf != orig_in)
		ck_free(in_buf);
	ck_free(out_buf);
	ck_free(eff_map);

	return ret_val;

#undef FLIP_BIT

}

/* Grab interesting test cases from other fuzzers. */

static void sync_fuzzers(char** argv)
{ //参数是启动qemu的参数

	DIR* sd;
	struct dirent* sd_ent;
	u32 sync_cnt = 0;

	sd = opendir(sync_dir); //sync_dir目录
	if (!sd)
		PFATAL("Unable to open '%s'",sync_dir);

	stage_max = stage_cur = 0;
	cur_depth = 0;

	/* Look at the entries created for every other fuzzer in the sync directory. */

	while ((sd_ent = readdir(sd)))
	{ //循环读取目录下的目录

		static u8 stage_tmp [ 128 ];

		DIR* qd;
		struct dirent* qd_ent;
		u8 *qd_path , *qd_synced_path;
		u32 min_accept = 0 , next_min_accept;

		s32 id_fd;

		/* Skip dot files and our own output directory. */

		if (sd_ent->d_name [ 0 ] == '.' || !strcmp(sync_id,sd_ent->d_name))
			continue;

		/* Skip anything that doesn't have a queue/ subdirectory. */

		qd_path = alloc_printf("%s/%s/queue",sync_dir,sd_ent->d_name); //指向一个fuzzer目录下的queue目录

		if (!(qd = opendir(qd_path)))
		{
			ck_free(qd_path);
			continue;
		}

		/* Retrieve the ID of the last seen test case. */
		//比如sync_dir/2/.synced/1   新见了一个目录,存放同步来的其他fuzzer下queue下的测试用例
		qd_synced_path = alloc_printf("%s/.synced/%s",out_dir,sd_ent->d_name);

		id_fd = open(qd_synced_path,O_RDWR | O_CREAT,0600);

		if (id_fd < 0)
			PFATAL("Unable to create '%s'",qd_synced_path);

		if (read(id_fd,&min_accept,sizeof(u32)) > 0)
			lseek(id_fd,0,SEEK_SET);

		next_min_accept = min_accept;

		/* Show stats */

		sprintf(stage_tmp,"sync %u",++sync_cnt); //状态叫做sync 1
		stage_name = stage_tmp;
		stage_cur = 0;
		stage_max = 0;

		/* For every file queued by this fuzzer, parse ID and see if we have looked at
		 it before; exec a test case if not. */

		while ((qd_ent = readdir(qd)))
		{ //读取某一个fuzzer下的queue目录

			u8* path;
			s32 fd;
			struct stat st;
			//这里syncing_case是从qd_ent->d_name中读取的
			if (qd_ent->d_name [ 0 ] == '.'
					|| sscanf(qd_ent->d_name,CASE_PREFIX "%06u",&syncing_case)
							!= 1 || syncing_case < min_accept)
				continue;

			/* OK, sounds like a new one. Let's give it a try. */

			if (syncing_case >= next_min_accept)
				next_min_accept = syncing_case + 1; //测试用例id的处理

			path = alloc_printf("%s/%s",qd_path,qd_ent->d_name); //指向被读取queue下的一个测试用例

			fd = open(path,O_RDONLY);
			if (fd < 0)
				PFATAL("Unable to open '%s'",path);

			if (fstat(fd,&st))
				PFATAL("fstat() failed");

			/* Ignore zero-sized or oversized files. */

			if (st.st_size && st.st_size <= MAX_FILE)
			{

				u8 fault;
				u8* mem = mmap(0,st.st_size,PROT_READ,MAP_PRIVATE,fd,0);

				if (mem == MAP_FAILED)
					PFATAL("Unable to mmap '%s'",path);

				/* See what happens. We rely on save_if_interesting() to catch major
				 errors and save the test case. */

				write_to_testcase(mem,st.st_size); //写入到当前的/output/.cur_input中

				fault = run_target(argv); //测试新的测试用例

				if (stop_soon)
					return;

				syncing_party = sd_ent->d_name;
				queued_imported += save_if_interesting(argv,mem,st.st_size,
						fault); //感兴趣就写入,然后queued_imported+1
				syncing_party = 0; //恢复

				munmap(mem,st.st_size);

				if (!(stage_cur++ % stats_update_freq))
					show_stats();

			}

			ck_free(path);
			close(fd);

		}

		ck_write(id_fd,&next_min_accept,sizeof(u32),qd_synced_path);

		close(id_fd);
		closedir(qd);
		ck_free(qd_path);
		ck_free(qd_synced_path);

	}

	closedir(sd);

}

/* Handle stop signal (Ctrl-C, etc). */

static void handle_stop_sig(int sig)
{

	stop_soon = 1;

	if (child_pid > 0)
		kill(child_pid,SIGKILL);
	if (forksrv_pid > 0)
		kill(forksrv_pid,SIGKILL);

}

/* Handle skip request (SIGUSR1). */

static void handle_skipreq(int sig)
{

	skip_requested = 1;

}

/* Handle timeout (SIGALRM). */

static void handle_timeout(int sig)
{

	if (child_pid > 0)
	{

		child_timed_out = 1;
		kill(child_pid,SIGKILL);

	}
	else if (child_pid == -1 && forksrv_pid > 0)
	{

		child_timed_out = 1;
		kill(forksrv_pid,SIGKILL);

	}

}

/* Do a PATH search and find target binary to see that it exists and
 isn't a shell script - a common and painful mistake. We also check for
 a valid ELF header and for evidence of AFL instrumentation. */

static void check_binary(u8* fname)
{

	u8* env_path = 0;
	struct stat st;

	s32 fd;
	u8* f_data;
	u32 f_len = 0;

	ACTF("Validating target binary...");

	if (strchr(fname,'/') || !(env_path = getenv("PATH")))
	{

		target_path = ck_strdup(fname);
		if (stat(target_path,&st) || !S_ISREG(st.st_mode)
				|| !(st.st_mode & 0111) || (f_len = st.st_size) < 4)
			FATAL("Program '%s' not found or not executable",fname);

	}
	else
	{

		while (env_path)
		{

			u8 *cur_elem , *delim = strchr(env_path,':');

			if (delim)
			{

				cur_elem = ck_alloc(delim - env_path + 1);
				memcpy(cur_elem,env_path,delim - env_path);
				delim++;

			}
			else
				cur_elem = ck_strdup(env_path);

			env_path = delim;

			if (cur_elem [ 0 ])
				target_path = alloc_printf("%s/%s",cur_elem,fname);
			else
				target_path = ck_strdup(fname);

			ck_free(cur_elem);

			if (!stat(target_path,&st) && S_ISREG(st.st_mode)
					&& (st.st_mode & 0111) && (f_len = st.st_size) >= 4)
				break;

			ck_free(target_path);
			target_path = 0;

		}

		if (!target_path)
			FATAL("Program '%s' not found or not executable",fname);

	}

	if (getenv("AFL_SKIP_BIN_CHECK"))
		return;

	/* Check for blatant user errors. */

	if ((!strncmp(target_path,"/tmp/",5) && !strchr(target_path + 5,'/'))
			|| (!strncmp(target_path,"/var/tmp/",9)
					&& !strchr(target_path + 9,'/')))
		FATAL("Please don't keep binaries in /tmp or /var/tmp");

	fd = open(target_path,O_RDONLY);

	if (fd < 0)
		PFATAL("Unable to open '%s'",target_path);

	f_data = mmap(0,f_len,PROT_READ,MAP_PRIVATE,fd,0);

	if (f_data == MAP_FAILED)
		PFATAL("Unable to mmap file '%s'",target_path);

	close(fd);

	if (f_data [ 0 ] == '#' && f_data [ 1 ] == '!')
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Oops, the target binary looks like a shell script. Some build systems will\n" "    sometimes generate shell stubs for dynamically linked programs; try static\n" "    library mode (./configure --disable-shared) if that's the case.\n\n"

				"    Another possible cause is that you are actually trying to use a shell\n" "    wrapper around the fuzzed component. Invoking shell can slow down the\n" "    fuzzing process by a factor of 20x or more; it's best to write the wrapper\n" "    in a compiled language instead.\n");

		FATAL("Program '%s' is a shell script",target_path);

	}

#ifndef __APPLE__

	if (f_data [ 0 ] != 0x7f || memcmp(f_data + 1,"ELF",3))

		#ifdef CGC
			if (f_data[0] != 0x7f || memcmp(f_data + 1, "CGC", 3)) //这里添加了cgc 判断
				FATAL("Program '%s' is not an ELF or CGC binary", target_path);
		#else
			FATAL("Program '%s' is not an ELF binary",target_path);
		#endif
#else

	if (f_data[0] != 0xCF || f_data[1] != 0xFA || f_data[2] != 0xED)
	FATAL("Program '%s' is not a 64-bit Mach-O binary", target_path);

#endif /* ^!__APPLE__ */

	if (!qemu_mode && !dumb_mode
			&& !memmem(f_data,f_len,SHM_ENV_VAR,strlen(SHM_ENV_VAR) + 1))
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Looks like the target binary is not instrumented! The fuzzer depends on\n" "    compile-time instrumentation to isolate interesting test cases while\n" "    mutating the input data. For more information, and for tips on how to\n" "    instrument binaries, please see %s/README.\n\n"

				"    When source code is not available, you may be able to leverage QEMU\n" "    mode support. Consult the README for tips on how to enable this.\n"

				"    (It is also possible to use afl-fuzz as a traditional, \"dumb\" fuzzer.\n" "    For that, you can use the -n option - but expect much worse results.)\n",
				doc_path);

		FATAL("No instrumentation detected");

	}

	if (qemu_mode && memmem(f_data,f_len,SHM_ENV_VAR,strlen(SHM_ENV_VAR) + 1))
	{

		SAYF(
				"\n" cLRD "[-] " cRST "This program appears to be instrumented with afl-gcc, but is being run in\n" "    QEMU mode (-Q). This is probably not what you want - this setup will be\n" "    slow and offer no practical benefits.\n");

		FATAL("Instrumentation found in -Q mode");

	}

	if (memmem(f_data,f_len,"libasan.so",10)
			|| memmem(f_data,f_len,"__msan_init",11))
		uses_asan = 1;

	/* Detect persistent & deferred init signatures in the binary. */

	if (memmem(f_data,f_len,PERSIST_SIG,strlen(PERSIST_SIG) + 1))
	{

		OKF(cPIN "Persistent mode binary detected.");
		setenv(PERSIST_ENV_VAR,"1",1);
		no_var_check = 1;

	}
	else if (getenv("AFL_PERSISTENT"))
	{

		WARNF("AFL_PERSISTENT is no longer supported and may misbehave!");

	}

	if (memmem(f_data,f_len,DEFER_SIG,strlen(DEFER_SIG) + 1))
	{

		OKF(cPIN "Deferred forkserver binary detected.");
		setenv(DEFER_ENV_VAR,"1",1);

	}
	else if (getenv("AFL_DEFER_FORKSRV"))
	{

		WARNF("AFL_DEFER_FORKSRV is no longer supported and may misbehave!");

	}

	if (munmap(f_data,f_len))
		PFATAL("unmap() failed");

}

/* Trim and possibly create a banner for the run. */

static void fix_up_banner(u8* name)
{

	if (!use_banner)
	{

		if (sync_id)
		{

			use_banner = sync_id;

		}
		else
		{

			u8* trim = strrchr(name,'/');
			if (!trim)
				use_banner = name;
			else
				use_banner = trim + 1;

		}

	}

	if (strlen(use_banner) > 40)
	{

		u8* tmp = ck_alloc(44);
		sprintf(tmp,"%.40s...",use_banner);
		use_banner = tmp;

	}

}

/* Check if we're on TTY. */

static void check_if_tty(void)
{

	struct winsize ws;

	if (ioctl(1,TIOCGWINSZ,&ws))
	{

		if (errno == ENOTTY)
		{
			OKF(
					"Looks like we're not running on a tty, so I'll be a bit less verbose.");
			not_on_tty = 1;
		}

		return;
	}

}

/* Check terminal dimensions after resize. */

static void check_term_size(void)
{

	struct winsize ws;

	term_too_small = 0;

	if (ioctl(1,TIOCGWINSZ,&ws))
		return;

	if (ws.ws_row < 25 || ws.ws_col < 80)
		term_too_small = 1;

}

/* Display usage hints. */

static void usage(u8* argv0)
{

	SAYF(
			"\n%s [ options ] -- /path/to/fuzzed_app [ ... ]\n\n"

					"Required parameters:\n\n"

					"  -i dir        - input directory with test cases\n"
					"  -o dir        - output directory for fuzzer findings\n\n"

					"Execution control settings:\n\n"

					"  -f file       - location read by the fuzzed program (stdin)\n"
					"  -N URL        - fuzzed program is to read from a network port.\n"
					"                  The network is specified by URL = type://path:port\n"
					"                  where type= {udp|tcp}, path={::1|127.0.0.1|localhost},\n"
					"                  and port is a port number or service name.\n"
					"                  There are two cases, where the target program to be\n"
					"                  fuzzed is either a server to afl-fuzz (the default)\n"
					"                  or a client of afl-fuzz (using the -L option).  If the\n"
					"                  target is a server, then afl-fuzz sends fuzzed data\n"
					"                  to the address and port specified in the URL.  If\n"
					"                  the target is a client, then afl-fuzz listens for\n"
					"                  data on the specified port and responds by sending\n"
					"                  fuzzed data to the (typically ephemeral) port used\n"
					"                  by the target.  Note that the '+' is likely to be\n"
					"                  necessary after the -t delay option for network\n"
					"                  fuzzing.\n"
					"  -D msec       - for network fuzzing only: delay in msec before\n"
					"                  a network read/write/connection is attempted;\n"
					"                  Note that 3 attempts are made, with this\n"
					"                  delay between each (-t is still in effect)\n"
					"  -L            - specify this option if the fuzzed program is a\n"
					"                  network client (meaning it writes to the network\n"
					"                  before reading (a fuzzed input) from the network.\n"
					"                  The port is the port number to which the network\n"
					"                  client is expected to write.\n"
					"  -t msec       - timeout for each run (auto-scaled, 50-%u ms)\n"
					"  -m megs       - memory limit for child process (%u MB)\n"
					"  -Q            - use binary-only instrumentation (QEMU mode)\n\n"

					"Fuzzing behavior settings:\n\n"

					"  -d            - quick & dirty mode (skips deterministic steps)\n"
					"  -n            - fuzz without instrumentation (dumb mode)\n"
					"  -x dir        - optional fuzzer dictionary (see README)\n\n"

					"Other stuff:\n\n"

					"  -T text       - text banner to show on the screen\n"
					"  -M / -S id    - distributed mode (see parallel_fuzzing.txt)\n"
					"  -C            - crash exploration mode (the peruvian rabbit thing)\n\n"

					"For additional tips, please consult %s/README.\n\n",

			argv0,EXEC_TIMEOUT,MEM_LIMIT,doc_path);

	exit(1);

}

/* Prepare output directories and fds. */

static void setup_dirs_fds(void)
{

	u8* tmp;
	s32 fd;

	ACTF("Setting up output directories...");

	if (sync_id && mkdir(sync_dir,0700) && errno != EEXIST)
		PFATAL("Unable to create '%s'",sync_dir);

	if (mkdir(out_dir,0700))
	{

		if (errno != EEXIST)
			PFATAL("Unable to create '%s'",out_dir);

		maybe_delete_out_dir(); //为了防止误删之前运行的结果

	}
	else
	{

		if (in_place_resume)
			FATAL("Resume attempted but old output directory not found");

		out_dir_fd = open(out_dir,O_RDONLY);

#ifndef __sun

		if (out_dir_fd < 0 || flock(out_dir_fd,LOCK_EX | LOCK_NB))
			PFATAL("Unable to flock() output directory.");

#endif /* !__sun */

	}

	/* Queue directory for any starting & discovered paths. */

	tmp = alloc_printf("%s/queue",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

#ifdef XIAOSA
	// mkdir  trace  catalog, to save the trace_bit of every testcase in queue catalog
	tmp = alloc_printf("%s/queue_trace_mini",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	// mkdir  trace  catalog, to save the trace_bit of every testcase in crash catalog
		tmp = alloc_printf("%s/crash_trace_mini",out_dir);
		if (mkdir(tmp,0700))
			PFATAL("Unable to create '%s'",tmp);
		ck_free(tmp);
#endif

	/* Top-level directory for queue metadata used for session
	 resume and related tasks. */

	tmp = alloc_printf("%s/queue/.state/",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* Directory for flagging queue entries that went through
	 deterministic fuzzing in the past. */

	tmp = alloc_printf("%s/queue/.state/deterministic_done/",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* Directory with the auto-selected dictionary entries. */

	tmp = alloc_printf("%s/queue/.state/auto_extras/",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* The set of paths currently deemed redundant. */

	tmp = alloc_printf("%s/queue/.state/redundant_edges/",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* The set of paths showing variable behavior. */

	tmp = alloc_printf("%s/queue/.state/variable_behavior/",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* Sync directory for keeping track of cooperating fuzzers. */

	if (sync_id)
	{

		tmp = alloc_printf("%s/.synced/",out_dir);
		if (mkdir(tmp,0700))
			PFATAL("Unable to create '%s'",tmp);
		ck_free(tmp);

	}

	/* All recorded crashes. */

	tmp = alloc_printf("%s/crashes",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* All recorded hangs. */

	tmp = alloc_printf("%s/hangs",out_dir);
	if (mkdir(tmp,0700))
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	/* Generally useful file descriptors. */

	dev_null_fd = open("/dev/null",O_RDWR);
	if (dev_null_fd < 0)
		PFATAL("Unable to open /dev/null");

	dev_urandom_fd = open("/dev/urandom",O_RDONLY);
	if (dev_urandom_fd < 0)
		PFATAL("Unable to open /dev/urandom");

	/* Gnuplot output file. */

	tmp = alloc_printf("%s/plot_data",out_dir);
	fd = open(tmp,O_WRONLY | O_CREAT | O_EXCL,0600);
	if (fd < 0)
		PFATAL("Unable to create '%s'",tmp);
	ck_free(tmp);

	plot_file = fdopen(fd,"w");
	if (!plot_file)
		PFATAL("fdopen() failed");

	fprintf(plot_file,"# unix_time, cycles_done, cur_path, paths_total, "
			"pending_total, pending_favs, map_size, unique_crashes, "
			"unique_hangs, max_depth, execs_per_sec\n");
	/* ignore errors */

}

/* Setup the output file for fuzzed data, if not using -f. */

static void setup_stdio_file(void)
{

	u8* fn = alloc_printf("%s/.cur_input",out_dir);

	unlink(fn); /* Ignore errors */

	out_fd = open(fn,O_RDWR | O_CREAT | O_EXCL,0600);

	if (out_fd < 0)
		PFATAL("Unable to create '%s'",fn);

	ck_free(fn);

}

/* Make sure that core dumps don't go to a program. */

static void check_crash_handling(void)
{

#ifdef __APPLE__

	/* Yuck! There appears to be no simple C API to query for the state of
	 loaded daemons on MacOS X, and I'm a bit hesitant to do something
	 more sophisticated, such as disabling crash reporting via Mach ports,
	 until I get a box to test the code. So, for now, we check for crash
	 reporting the awful way. */

	if (system("launchctl list 2>/dev/null | grep -q '\\.ReportCrash$'")) return;

	SAYF("\n" cLRD "[-] " cRST
			"Whoops, your system is configured to forward crash notifications to an\n"
			"    external crash reporting utility. This will cause issues due to the\n"
			"    extended delay between the fuzzed binary malfunctioning and this fact\n"
			"    being relayed to the fuzzer via the standard waitpid() API.\n\n"
			"    To avoid having crashes misinterpreted as hangs, please run the\n"
			"    following commands:\n\n"

			"    SL=/System/Library; PL=com.apple.ReportCrash\n"
			"    launchctl unload -w ${SL}/LaunchAgents/${PL}.plist\n"
			"    sudo launchctl unload -w ${SL}/LaunchDaemons/${PL}.Root.plist\n");

	if (!getenv("AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES"))
	FATAL("Crash reporter detected");

#else

	/* This is Linux specific, but I don't think there's anything equivalent on
	 *BSD, so we can just let it slide for now. */

	s32 fd = open("/proc/sys/kernel/core_pattern",O_RDONLY);
	u8 fchar;

	if (fd < 0)
		return;

	ACTF("Checking core_pattern...");

	if (read(fd,&fchar,1) == 1 && fchar == '|')
	{

		SAYF(
				"\n" cLRD "[-] " cRST "Hmm, your system is configured to send core dump notifications to an\n" "    external utility. This will cause issues due to an extended delay\n" "    between the fuzzed binary malfunctioning and this information being\n" "    eventually relayed to the fuzzer via the standard waitpid() API.\n\n"

				"    To avoid having crashes misinterpreted as hangs, please log in as root\n" "    and temporarily modify /proc/sys/kernel/core_pattern, like so:\n\n"

				"    echo core >/proc/sys/kernel/core_pattern\n");

		if (!getenv("AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES"))
			FATAL("Pipe at the beginning of 'core_pattern'");

	}

	close(fd);

#endif /* ^__APPLE__ */

}

/* Check CPU governor. */

static void check_cpu_governor(void)
{

	FILE* f;
	u8 tmp [ 128 ];
	u64 min = 0 , max = 0;

	if (getenv("AFL_SKIP_CPUFREQ"))
		return;

	f = fopen("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor","r");
	if (!f)
		return;

	ACTF("Checking CPU scaling governor...");

	if (!fgets(tmp,128,f))
		PFATAL("fgets() failed");

	fclose(f);

	if (!strncmp(tmp,"perf",4))
		return;

	f = fopen("/sys/devices/system/cpu/cpu0/cpufreq/scaling_min_freq","r");

	if (f)
	{
		if (fscanf(f,"%llu",&min) != 1)
			min = 0;
		fclose(f);
	}

	f = fopen("/sys/devices/system/cpu/cpu0/cpufreq/scaling_max_freq","r");

	if (f)
	{
		if (fscanf(f,"%llu",&max) != 1)
			max = 0;
		fclose(f);
	}

	if (min == max)
		return;

	SAYF(
			"\n" cLRD "[-] " cRST "Whoops, your system uses on-demand CPU frequency scaling, adjusted\n" "    between %llu and %llu MHz. Unfortunately, the scaling algorithm in the\n" "    kernel is imperfect and can miss the short-lived processes spawned by\n" "    afl-fuzz. To keep things moving, run these commands as root:\n\n"

			"    cd /sys/devices/system/cpu\n" "    echo performance | tee cpu*/cpufreq/scaling_governor\n\n"

			"    You can later go back to the original state by replacing 'performance' with\n" "    'ondemand'. If you don't want to change the settings, set AFL_SKIP_CPUFREQ\n" "    to make afl-fuzz skip this check - but expect some performance drop.\n",
			min / 1024,max / 1024);

	FATAL("Suboptimal CPU scaling governor");

}

/* Count the number of logical CPU cores. */

static void get_core_count(void)
{

	u32 cur_runnable = 0;

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)

	size_t s = sizeof(cpu_core_count);

	/* On *BSD systems, we can just use a sysctl to get the number of CPUs. */

#ifdef __APPLE__

	if (sysctlbyname("hw.logicalcpu", &cpu_core_count, &s, NULL, 0) < 0)
	return;

#else

	int s_name[2] =
	{	CTL_HW, HW_NCPU};

	if (sysctl(s_name, 2, &cpu_core_count, &s, NULL, 0) < 0) return;

#endif /* ^__APPLE__ */

#else

	/* On Linux, a simple way is to look at /proc/stat, especially since we'd
	 be parsing it anyway for other reasons later on. */

	FILE* f = fopen("/proc/stat","r");
	u8 tmp [ 1024 ];

	if (!f)
		return;

	while (fgets(tmp,sizeof(tmp),f))
		if (!strncmp(tmp,"cpu",3) && isdigit(tmp [ 3 ]))
			cpu_core_count++;

	fclose(f);

#endif /* ^(__APPLE__ || __FreeBSD__ || __OpenBSD__) */

	if (cpu_core_count)
	{

		cur_runnable = (u32) get_runnable_processes();

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)

		/* Add ourselves, since the 1-minute average doesn't include that yet. */

		cur_runnable++;

#endif /* __APPLE__ || __FreeBSD__ || __OpenBSD__ */

		OKF(
				"You have %u CPU cores and %u runnable tasks (utilization: %0.0f%%).",
				cpu_core_count,cur_runnable,
				cur_runnable * 100.0 / cpu_core_count);

		if (cpu_core_count > 1)
		{

			if (cur_runnable > cpu_core_count * 1.5)
			{

				WARNF("System under apparent load, performance may be spotty.");

			}
			else if (cur_runnable + 1 <= cpu_core_count)
			{

				OKF("Try parallel jobs - see %s/parallel_fuzzing.txt.",
						doc_path);

			}

		}

	}
	else
		WARNF("Unable to figure out the number of CPU cores.");

}

/* Validate and fix up out_dir and sync_dir when using -S. */

static void fix_up_sync(void)
{

	u8* x = sync_id;

	if (dumb_mode)
		FATAL("-S / -M and -n are mutually exclusive");

	if (skip_deterministic)
	{

		if (force_deterministic)
			FATAL("use -S instead of -M -d");
		else
			FATAL("-S already implies -d");

	}

	while (*x)
	{ //名字判定

		if (!isalnum(*x) && *x != '_' && *x != '-')
			FATAL("Non-alphanumeric fuzzer ID specified via -S or -M");

		x++;

	}

	if (strlen(sync_id) > 32)
		FATAL("Fuzzer ID too long");

	x = alloc_printf("%s/%s",out_dir,sync_id); //配置目录

	sync_dir = out_dir;
	out_dir = x;

	if (!force_deterministic)
	{
		skip_deterministic = 1;
		use_splicing = 1;
	}

}

/* Handle screen resize (SIGWINCH). */

static void handle_resize(int sig)
{
	clear_screen = 1;
}

/* Check ASAN options. */

static void check_asan_opts(void)
{
	u8* x = getenv("ASAN_OPTIONS");

	if (x && !strstr(x,"abort_on_error=1"))
		FATAL("Custom ASAN_OPTIONS set without abort_on_error=1 - please fix!");

	x = getenv("MSAN_OPTIONS");

	if (x && !strstr(x,"exit_code=" STRINGIFY(MSAN_ERROR)))
		FATAL(
				"Custom MSAN_OPTIONS set without exit_code=" STRINGIFY(MSAN_ERROR) " - please fix!");

}

/* Detect @@ in args. */

static void detect_file_args(char** argv)
{ //这个argv的位置

	u32 i = 0;
	u8* cwd = getcwd(NULL,0); //获取当前工作目录,字符串大小会自动配置

	if (!cwd)
		PFATAL("getcwd() failed");

	while (argv [ i ])
	{

		u8* aa_loc = strstr(argv [ i ],"@@"); //返回@@在argv[i]中首次出现的地址,否则返回null

		if (aa_loc)
		{

			u8 *aa_subst , *n_arg;

			/* If we don't have a file name chosen yet, use a safe default. */

			if (!out_file)
				out_file = alloc_printf("%s/.cur_input",out_dir);

			/* Be sure that we're always using fully-qualified paths. */

			if (out_file [ 0 ] == '/')
				aa_subst = out_file;
			else
				aa_subst = alloc_printf("%s/%s",cwd,out_file); //使用全路径形式.

			/* Construct a replacement argv value. */

			*aa_loc = 0;
			n_arg = alloc_printf("%s%s%s",argv [ i ],aa_subst,aa_loc + 2);
			argv [ i ] = n_arg;
			*aa_loc = '@';

			if (out_file [ 0 ] != '/')
				ck_free(aa_subst);

		}

		i++;

	}

	free(cwd); /* not tracked */

}

/* Set up signal handlers. More complicated that needs to be, because libc on
 Solaris doesn't resume interrupted reads(), sets SA_RESETHAND when you call
 siginterrupt(), and does other stupid things. */

static void setup_signal_handlers(void)
{

	struct sigaction sa;

	sa.sa_handler = NULL;
	sa.sa_flags = SA_RESTART;
	sa.sa_sigaction = NULL;

	sigemptyset(&sa.sa_mask);

	/* Various ways of saying "stop". */

	sa.sa_handler = handle_stop_sig;
	sigaction(SIGHUP,&sa,NULL);
	sigaction(SIGINT,&sa,NULL);
	sigaction(SIGTERM,&sa,NULL);

	/* Exec timeout notifications. */

	sa.sa_handler = handle_timeout;
	sigaction(SIGALRM,&sa,NULL);

	/* Window resize */

	sa.sa_handler = handle_resize;
	sigaction(SIGWINCH,&sa,NULL);

	/* SIGUSR1: skip entry */

	sa.sa_handler = handle_skipreq;
	sigaction(SIGUSR1,&sa,NULL);

	/* Things we don't care about. */

	sa.sa_handler = SIG_IGN;
	sigaction(SIGTSTP,&sa,NULL);
	sigaction(SIGPIPE,&sa,NULL);

}

/* Rewrite argv for QEMU. */
//argv是 aflout2  .cur_input 	 2个参数
static char** get_qemu_argv(u8* own_loc, char** argv, int argc)
{

	char** new_argv = ck_alloc(sizeof(char*) * (argc + 4));
	u8 *tmp , *cp , *rsl , *own_copy;

	memcpy(new_argv + 3,argv + 1,sizeof(char*) * argc); //将 .cur_input赋值给new_argv

	new_argv [ 2 ] = target_path;
	new_argv [ 1 ] = "--";
	//最后是 `-- aflout2 .cur_intput`
	/* Now we need to actually find the QEMU binary to put in argv[0]. */

	tmp = getenv("AFL_PATH");

	if (tmp)
	{

		cp = alloc_printf("%s/afl-qemu-trace",tmp);

		if (access(cp,X_OK))
			FATAL("Unable to find '%s'",tmp);

		target_path = new_argv [ 0 ] = cp;
		return new_argv;

	}

	own_copy = ck_strdup(own_loc); //取 afl-fuzz所在的目录
	rsl = strrchr(own_copy,'/');

	if (rsl)
	{

		*rsl = 0;

		cp = alloc_printf("%s/afl-qemu-trace",own_copy); //cp指向afl-yyy/afl-qemu-trace
		ck_free(own_copy);

		if (!access(cp,X_OK))
		{
			//没有执行权限
			target_path = new_argv [ 0 ] = cp; //最后new_argv是`afl-qemu-trace -- aflout2 .cur_intput`
			return new_argv;

		}

	}
	else
		ck_free(own_copy);

	if (!access(BIN_PATH "/afl-qemu-trace", X_OK))
	{

		target_path = new_argv[0] = ck_strdup(BIN_PATH "/afl-qemu-trace");
		return new_argv;

	}

	SAYF(
			"\n" cLRD "[-] " cRST "Oops, unable to find the 'afl-qemu-trace' binary. The binary must be built\n" "    separately by following the instructions in qemu_mode/README.qemu. If you\n" "    already have the binary installed, you may need to specify AFL_PATH in the\n" "    environment.\n\n"

			"    Of course, even without QEMU, afl-fuzz can still work with binaries that are\n" "    instrumented at compile time with afl-gcc. It is also possible to use it as a\n" "    traditional \"dumb\" fuzzer by specifying '-n' in the command line.\n");

	FATAL("Failed to locate 'afl-qemu-trace'.");

}

/* Make a copy of the current command line. */

static void save_cmdline(u32 argc, char** argv)
{

	u32 len = 1 , i;
	u8* buf;

	for (i = 0; i < argc; i++)
		len += strlen(argv [ i ]) + 1;

	buf = orig_cmdline = ck_alloc(len);

	for (i = 0; i < argc; i++)
	{

		u32 l = strlen(argv [ i ]);

		memcpy(buf,argv [ i ],l);
		buf += l;

		if (i != argc - 1)
			*(buf++) = ' ';

	}

	*buf = 0; //命令行中的值保存在buf中,然后呢?

}



#ifdef XIAOSA
//Functions by xiaosatianyu,just before the main function

//save the times about the tuple execution number
static void y_save_tuple_execution_num()
{
	u32 i = 0;
	u8 * tmpy = "";
	int fdy;
	tmpy = alloc_printf("%s/executed_num",out_dir);
	remove(tmpy);
	fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600);
	if (fdy < 0)
		PFATAL("Unable to create '%s'",tmpy);
	ck_free(tmpy);
	for (i = 0; i < MAP_SIZE; i++)
	{
		if (virgin_counts [ i ] != 0)
		{

			tmpy = alloc_printf("NO.%-6u is executed %-20u times;\n",i,
					virgin_counts [ i ]);
			ck_write(fdy,tmpy,strlen(tmpy),"executed_num file");
			ck_free(tmpy);
		}

	}
	close(fdy);
}

//save the informaiton about the big cycle
static void y_save_information_big_cycle()
{
	u8* tmpy="";
	int fdy;
	//记录每一次大循环的起始和结束时间,这个大循环增加的测试用例数量

	//open then target file
	tmpy = alloc_printf("%s/big_cycle_information",out_dir);
	fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
	if (fdy < 0)
		PFATAL("Unable to open '%s'","out_dir/big_cycle_information");
	ck_free(tmpy);

	if (queued_paths == queued_at_start)
	{
		//if the first
		big_cycle_start_time = get_cur_time(); //first big cycle

		//save the initial information about the queue and crash catalog
		last_big_cycle_case_num = queued_at_start; //intial number of the testcase
		last_big_cycle_crash_num = 0;	//intial number of the crash
		tmpy = alloc_printf("the initial testcase number is %d.\n"
				"the initial crash number is %d\n\n",queued_at_start,
				last_big_cycle_crash_num);
		ck_write(fdy,tmpy,strlen(tmpy),"big_cycle_information");
		ck_free(tmpy);
		close(fdy);
	}
	else
	{
		//calculate the time
		big_cycle_stop_time = get_cur_time(); // the stop time of the big cycle

		time_of_big_cycle = (big_cycle_stop_time - big_cycle_start_time) / 1000; //second level

		//save the added number of the testcase in the queue and crash catalog
		//the queue catalog
		add_case_num_last_big_cycle = queued_paths - last_big_cycle_case_num;
		last_big_cycle_case_num = queued_paths;

		//the crash catalog
		add_crash_num_last_big_cycle = unique_crashes
				- last_big_cycle_crash_num;
		last_big_cycle_crash_num = unique_crashes;

		//save to the file
		tmpy = alloc_printf(
				"the add number of the testcase in the NO.%llu cycle is %u, "
				"the total number of the testcase is %u\n"
				"the add number of the crash in the NO.%llu cycle is %u, "
				"the total number of the crash is %llu\n"
				"the consume time is %-30s \n\n",
				queue_cycle ,
				add_case_num_last_big_cycle,queued_paths,
				queue_cycle ,
				add_crash_num_last_big_cycle,unique_crashes,
				DTD(big_cycle_stop_time,big_cycle_start_time));
		ck_write(fdy,tmpy,strlen(tmpy),"big_cycle_information");
		ck_free(tmpy);
		close(fdy);

		big_cycle_start_time = big_cycle_stop_time;	//reset the start time of the next big cycle
	}

}

//save the informaition when the the fuzzone function end
//save the time and the child number
static void y_save_fuzzone_end_each_cycle()
{
	u8* tmpy = "";
	int fdy;
	//记录每一次大循环的起始和结束时间,这个大循环增加的测试用例数量

	//open then target file
	//tmpy = alloc_printf("%s/fuzz_one_end_in_cycle%llu",out_dir,queue_cycle);
	tmpy = alloc_printf("%s/fuzz_one_end",out_dir);
	fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
	if (fdy < 0)
		PFATAL("Unable to open '%s'","out_dir/big_cycle_information");
	ck_free(tmpy);

	tmpy =alloc_printf(
		  "%u cycle %llu fuzzone %s,child:%u,crash:%u,bit_size:%u,%s in_top_rate,len:%u\n",
		  queue_cur->self_id,queue_cycle,queue_cur->fuzz_one_time,queue_cur->nm_child,queue_cur->nm_crash_child,
		  queue_cur->bitmap_size, queue_cur->in_top_rate?"":"not",queue_cur->len
		 );
	ck_write(fdy,tmpy,strlen(tmpy),"fuzz_one_end");
	ck_free(tmpy);
	close(fdy);

}



/* Get unix time in microseconds  at main function begin*/ //微秒
static u64 y_get_cur_time_us_at_start(void)
{

	struct timeval tv;
	struct timezone tz;

	gettimeofday(&tv,&tz); //系统api,获取时间

	return (tv.tv_sec * 1000000ULL) + tv.tv_usec; //返回的是微秒

}


#endif //end  #ifdef XIAOSA



/* Main entry point */

int main(int argc, char** argv)
{
#ifdef XIAOSA
	//record the start time at main function
	main_start_time=y_get_cur_time_us_at_start();
#endif

	s32 opt;
	u64 prev_queued = 0;
	u32 sync_interval_cnt = 0 , seek_to;
	u8 *extras_dir = 0;
	u8 mem_limit_given = 0;
#ifdef XIAOSA
	u64 fuzz_start_us , fuzz_stop_us; // to remark the time of function fuzzone
	s32 fdy; //file IO
	u8 *tmpy = ""; ///yyy temp alloc
#endif

	/* add the "digraph graphname{" in the last place of the file of /tmp/trace */

	char** use_argv;

	SAYF(cCYA "afl-fuzz " cBRI VERSION cRST " by <lcamtuf@google.com>\n");

	doc_path = access(DOC_PATH,F_OK) ? "docs" : DOC_PATH; //doc_path is static variable

	while ((opt = getopt(argc,argv,"+i:o:f:m:t:T:dnCB:S:M:x:QN:D:L")) > 0)
	{ //getopt 系统调用

		switch (opt)
		{

			case 'i' :

				if (in_dir)
					FATAL("Multiple -i options not supported");
				in_dir = optarg; //配置输入测试用例的目录

				if (!strcmp(in_dir,"-"))
					in_place_resume = 1;  //strcmp 比较连个字符串

				break;

			case 'o' : /* output dir */

				if (out_dir)
					FATAL("Multiple -o options not supported");
				out_dir = optarg; //输出结构的目录
				break;

			case 'M' :

				force_deterministic = 1;
				/* Fall through */

			case 'S' : /* sync ID */

				if (sync_id)
					FATAL("Multiple -S or -M options not supported");
				sync_id = optarg;
				break;

			case 'f' : /* target file */

				if (out_file)
					FATAL("Multiple -f options not supported");
				out_file = optarg;
				break;

			case 'x' :

				if (extras_dir)
					FATAL("Multiple -x options not supported");
				extras_dir = optarg;
				break;

			case 't' :
			{

				u8 suffix = 0;

				if (timeout_given)
					FATAL("Multiple -t options not supported");

				if (sscanf(optarg,"%u%c",&exec_tmout,&suffix) < 1
						|| optarg [ 0 ] == '-')
					FATAL("Bad syntax used for -t");

				if (exec_tmout < 5)
					FATAL("Dangerously low value of -t");

				if (suffix == '+')
					timeout_given = 2;
				else
					timeout_given = 1;

				break;

			}

			case 'm' :
			{

				u8 suffix = 'M';

				if (mem_limit_given)
					FATAL("Multiple -m options not supported");
				mem_limit_given = 1;

				if (!strcmp(optarg,"none"))
				{

					mem_limit = 0;
					break;

				}

				if (sscanf(optarg,"%llu%c",&mem_limit,&suffix) < 1
						|| optarg [ 0 ] == '-')
					FATAL("Bad syntax used for -m");

				switch (suffix)
				{

					case 'T' :
						mem_limit *= 1024 * 1024;
						break;
					case 'G' :
						mem_limit *= 1024;
						break;
					case 'k' :
						mem_limit /= 1024;
						break;
					case 'M' :
						break;

					default :
						FATAL("Unsupported suffix or bad syntax for -m");

				}

				if (mem_limit < 5)
					FATAL("Dangerously low value of -m");

				if (sizeof(rlim_t) == 4 && mem_limit > 2000)
					FATAL("Value of -m out of range on 32-bit systems");

			}

				break;

			case 'd' :

				if (skip_deterministic)
					FATAL("Multiple -d options not supported");
				skip_deterministic = 1;
				use_splicing = 1;
				break;

			case 'B' :

				/* This is a secret undocumented option! It is useful if you find
				 an interesting test case during a normal fuzzing process, and want
				 to mutate it without rediscovering any of the test cases already
				 found during an earlier run.

				 To use this mode, you need to point -B to the fuzz_bitmap produced
				 by an earlier run for the exact same binary... and that's it.

				 I only used this once or twice to get variants of a particular
				 file, so I'm not making this an official setting. */

				if (in_bitmap)
					FATAL("Multiple -B options not supported");

				in_bitmap = optarg;
				read_bitmap(in_bitmap); //读取到virgin_bits
				break;

			case 'C' :

				if (crash_mode)
					FATAL("Multiple -C options not supported");
				crash_mode = FAULT_CRASH;
				break;

			case 'n' :

				if (dumb_mode)
					FATAL("Multiple -n options not supported");
				if (getenv("AFL_DUMB_FORKSRV"))
					dumb_mode = 2;
				else
					dumb_mode = 1;

				break;

			case 'T' :

				if (use_banner)
					FATAL("Multiple -T options not supported");
				use_banner = optarg;
				break;

			case 'Q' :

				if (qemu_mode)
					FATAL("Multiple -Q options not supported");
				qemu_mode = 1;

				if (!mem_limit_given)
					mem_limit = MEM_LIMIT_QEMU; //限制qemu的内存上限

				break;

			case 'N' :

				/* -N{network-path} : inject data to target via network connection
				 *
				 * The network-path has the form "type://path:port" where
				 *
				 * type is one of "udp", or "tcp",
				 * path is a host name or IP address (IPv4 or IPv6), and
				 * port is a port number or service name.
				 *
				 * for the moment, make a copy of the -N option string and
				 * indicate that the -N option has been specified
				 *
				 */

				if (N_option_specified)
					FATAL("multiple -N options not allowed");
				N_slen = strlen(optarg);
				if (N_slen > 0)
				{
					N_option_string = (u8*) ck_alloc(N_slen + 1);
					strcpy(N_option_string,optarg);
					N_option_specified = 1;
				}
				else
				{
					FATAL("-N: missing argument");
				}
				break;

			case 'D' :

				if (N_timeout_given)
					FATAL("Multiple -D options not supported");
				if (sscanf(optarg,"%u",&N_exec_tmout) < 1
						|| optarg [ 0 ] == '-')
					FATAL("Bad syntax used for -D");
				N_timeout_given = 1;
				break;

			case 'L' :

				if (N_fuzz_client)
					FATAL("Multiple -L options not supported");
				N_fuzz_client = 1;
				break;

			default :

				usage(argv [ 0 ]);

		}
	}

	/* check for consistent use of network options (-N, -D, and -L) */
	if (N_fuzz_client && !N_option_specified)
		FATAL("-L (network client) option requires -N (network) option");
	if (N_timeout_given && !N_option_specified)
		FATAL("-D option can not be used without -N option");

	/* process network option(s), creating and configuring socket */
	if (N_option_specified)
	{

		/* local variables (not needed later):      */
		struct addrinfo N_hints; /* used for getaddrinfo() call */
		/* These are all pointers used to process the -N network-path        */
		u8 *N_found1 = 0 , *N_found2 = 0 , *N_pchar , *N_type;
		u8 *N_servicename = 0 , /* ptr to start of servicename */
		*N_hostspec = 0; /* ptr to start of hostname    */

		/* prepare (zero) addrinfo structure used for hints to getaddrinfo()*/
		memset(&N_hints,0,sizeof(struct addrinfo));

		/* process the -N option string -- two cases depending on N_fuzz_client */
		if (N_fuzz_client)
		{
			/* this is the case where afl-fuzz listens for the target to either
			 * connect and write (TCP) to afl-fuzz's socket or create a socket
			 * and send to (UDP) the afl-fuzz socket. */
			N_found1 = strpbrk(N_option_string,"://");
			if (!N_found1)
			{
				FATAL("-N: invalid specification");
			}
			else
			{
				if (*N_found1 != ':')
					FATAL("-N: first char after type must be ':'");
				N_type = N_option_string;
				*N_found1 = 0;
				N_pchar = N_type;
				while (*N_pchar != 0)
				{
					*N_pchar = tolower(*N_pchar);
					++N_pchar;
				}
				if (strcmp(N_type,"tcp") == 0)
				{
					N_hints.ai_flags = (AI_PASSIVE);
					N_hints.ai_family = AF_UNSPEC;
					N_hints.ai_socktype = SOCK_STREAM;
				}
				else if (strcmp(N_type,"udp") == 0)
				{
					N_hints.ai_flags = (AI_PASSIVE /* | AI_NUMERICSERV */); //COMMENTED OUT
					N_hints.ai_family = AF_UNSPEC;
					N_hints.ai_socktype = SOCK_DGRAM;
				}
				else
				{
					FATAL("-N: invalid type");
				}
			}

			if ((N_found1 - N_option_string) >= N_slen)
				FATAL("-N: incomplete specification");

			/* find the port number */
			N_found2 = strrchr(N_found1 + 1,':');
			if (!N_found2)
			{
				FATAL("-N: TCP and UDP operation require a port number");
			}
			else
			{
				*N_found2 = 0;
				if (*(N_found2 + 1) == 0)
				{
					FATAL("-N: no port number or service name specified");
				}
				else
				{
					N_servicename = N_found2 + 1;
				}
			}

			if ((strncmp(N_found1 + 1,"//",2)) != 0)
			{
				FATAL("-N: invalid network specification - malformed \"://\"");
			}
			else
			{
				*N_found1 = 0;
				N_hostspec = N_found1 + 3;
			}
			if (!((strcmp("localhost",N_hostspec) == 0)
					|| (strcmp("::1",N_hostspec) == 0)
					|| (strcmp("127.0.0.1",N_hostspec) == 0)))
				FATAL(
						"-N: only hosts allowed are localhost, ::1, and 127.0.0.1");

			if (strcmp("localhost",N_hostspec) == 0)
			{
				N_hints.ai_family = AF_UNSPEC;
			}
			else if (strcmp("::1",N_hostspec) == 0)
			{
				N_hints.ai_family = AF_INET6;
			}
			else
			{
				N_hints.ai_family = AF_INET;
			}
			if (getaddrinfo(N_hostspec,N_servicename,&N_hints,&N_results) != 0)
			{
				FATAL("-N: getaddrinfo() lookup failed");
			}
			else
			{
				N_valid = 1;
			}
		}
		else
		{
			/* This is the case where afl-fuzz either connects to the target
			 * and writes (TCP) or creates a socket and sends to the target (UDP). */
			N_found1 = strpbrk(N_option_string,"://");
			if (!N_found1)
			{
				FATAL("-N: invalid specification");
			}
			else
			{
				if (*N_found1 != ':')
					FATAL("-N: first char after type must be ':'");
				N_type = N_option_string;
				*N_found1 = 0;
				N_pchar = N_type;
				while (*N_pchar != 0)
				{
					*N_pchar = tolower(*N_pchar);
					++N_pchar;
				}
				if (strcmp(N_type,"tcp") == 0)
				{
					N_hints.ai_flags = (AI_V4MAPPED | AI_ADDRCONFIG);
					N_hints.ai_family = AF_UNSPEC;
					N_hints.ai_socktype = SOCK_STREAM;
				}
				else if (strcmp(N_type,"udp") == 0)
				{
					N_hints.ai_flags = (AI_V4MAPPED | AI_ADDRCONFIG);
					N_hints.ai_family = AF_UNSPEC;
					N_hints.ai_socktype = SOCK_DGRAM;
				}
				else
				{
					FATAL("-N: invalid type");
				}
			}

			if ((N_found1 - N_option_string) >= N_slen)
				FATAL("-N: incomplete specification");

			if (N_hints.ai_family == AF_UNSPEC)
			{ //redundant - for future use
				/* TCP and UDP operation require a port number */
				N_found2 = strrchr(N_found1 + 1,':');
				if (!N_found2)
				{
					FATAL("-N: TCP and UDP operation require a port number");
				}
				else
				{
					*N_found2 = 0;
					if (*(N_found2 + 1) == 0)
					{
						FATAL("-N: no port number or service name specified");
					}
					else
					{
						N_servicename = N_found2 + 1;
					}
				}
			}

			if ((strncmp(N_found1 + 1,"//",2)) != 0)
			{
				FATAL("-N: invalid network specification - malformed \"://\"");
			}
			else
			{
				*N_found1 = 0;
				N_hostspec = N_found1 + 3;
			}
			if (!((strcmp("localhost",N_hostspec) == 0)
					|| (strcmp("::1",N_hostspec) == 0)
					|| (strcmp("127.0.0.1",N_hostspec) == 0)))
				FATAL(
						"-N: only hosts allowed are localhost, ::1, and 127.0.0.1");

			if (N_hints.ai_family == AF_UNSPEC)
			{
				if (getaddrinfo(N_hostspec,N_servicename,&N_hints,&N_results)
						!= 0)
				{
					FATAL("-N: getaddrinfo() lookup failed");
				}
				else
				{
					N_valid = 1;
				}
			}
		}
	}

	//  exit(0); //TESTING

	if (optind == argc || !in_dir || !out_dir)
		usage(argv [ 0 ]); //判断参数完整性

	setup_signal_handlers(); //注册了子进程的监视信号
	check_asan_opts(); //asan是什么

	if (sync_id)
		fix_up_sync(); //配置第二个fuzz,修改了同步情况下的目录

	if (!strcmp(in_dir,out_dir))
		FATAL("Input and output directories can't be the same");

	if (dumb_mode)
	{

		if (crash_mode)
			FATAL("-C and -n are mutually exclusive");
		if (qemu_mode)
			FATAL("-Q and -n are mutually exclusive");

	}

	if (getenv("AFL_NO_FORKSRV"))
		no_forkserver = 1;
	if (getenv("AFL_NO_CPU_RED"))
		no_cpu_meter_red = 1;
	if (getenv("AFL_NO_VAR_CHECK"))
		no_var_check = 1;

	if (dumb_mode == 2 && no_forkserver)
		FATAL("AFL_DUMB_FORKSRV and AFL_NO_FORKSRV are mutually exclusive");

	save_cmdline(argc,argv);

	fix_up_banner(argv [ optind ]);

	check_if_tty();

	get_core_count();
	check_crash_handling(); //往系统中添加一些configure
	check_cpu_governor(); //处理核心模式,ok

	setup_post(); //不管
	setup_shm(); //trace_bits指针(静态)指向该共享内存.

	setup_dirs_fds(); //创建各种目录
	read_testcases(); //将测试用例添加到queue栈中,调用add_to_queue函数,添加到变量queue下
	load_auto(); //extras方面

	pivot_inputs(); //处理input,转移到/output/queue目录下   pivot 转移

	if (extras_dir)
		load_extras(extras_dir);

	if (!timeout_given)
		find_timeout(); //还不理解,大概是设置时间的
	//即从文件中读取,将文件指向测试用例
	detect_file_args(argv + optind + 1); //查看最后是否有@@符号.将指向@@参数的指针修改成指向.cur_input

	if (!out_file)
		setup_stdio_file(); //设置.cur_input文件

	check_binary(argv [ optind ]);

	start_time = get_cur_time();//运行开始时间

	if (qemu_mode)
		//argv[0]指向afl-fuzz
		//argv + optind指向目标程序
		//最后返回值是`afl-qemu-trace  --  aflout2 .cur_intput`
		//argc-optind表示use_argv中参数的个数
		use_argv = get_qemu_argv(argv [ 0 ],argv + optind,argc - optind); //获得启动qemu的参数, 只有目标程序
	else
		use_argv = argv + optind; //执行的程序以及参数

	//在配置信息结束后,正式运行前比较合适
#ifdef XIAOSA

	//--------------------
	tmpy = alloc_printf("%s/test_add.plot",out_dir);
	remove(tmpy);
	fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
	if (fdy < 0)
		PFATAL("Unable to create '%s'","out_dir/test_add.plot");
	ck_free(tmpy);

	tmpy = alloc_printf("digraph graphname{\n"
			"	node[fontsize=\"10,10\"];\n"
			"	edge[style=\"bold\",fontsize=\"10,10\"];\n"
			"	graph[fontname = \"Helvetica-Oblique\",\n"
			"		size = \"100000,100000\",\n"
			"		ratio=1.2 ];\n"); //提前写入头信息
	ck_write(fdy,tmpy,strlen(tmpy),"test_add.plot");
	ck_free(tmpy);
	close(fdy);
	//--------------------
	//保存冗余的例子
	tmpy = alloc_printf("%s/redundant_edges",out_dir);
	remove(tmpy);
	ck_free(tmpy);

	//冗余恢复的例子
	tmpy = alloc_printf("%s/redundant_resume",out_dir);
	remove(tmpy);
	ck_free(tmpy);

	//保存每次大循环信息的文件
	tmpy = alloc_printf("%s/big_cycle_information",out_dir);
	remove(tmpy); //冗余恢复的例子
	ck_free(tmpy);

	//remove the old file for the function of y_save_fuzzone_end_each_cycle
	tmpy = alloc_printf("%s/fuzz_one_end",out_dir);
	remove(tmpy);
	ck_free(tmpy);

#endif

	perform_dry_run(use_argv); //测试初始测试用例的可用性吧?! ,形成了一个top_rated数组

	cull_queue(); //进一步优化测试用例

	show_init_stats(); //图像数据显示

	seek_to = find_start_position(); //从暂停点重启,暂时不管

	write_stats_file(0,0); //保存fuzz的信息到/output/fuzzer_stats
	save_auto(); //extras方面

	if (stop_soon)
		goto stop_fuzzing;

	/* Woop woop woop */

	if (!not_on_tty)
	{
#ifndef XIAOSA
		sleep(4);
		start_time += 4000;
#endif
		if (stop_soon)
			goto stop_fuzzing;
	}

	while (1)
	{ //死循环,一直跑

		u8 skipped_fuzz;
#ifdef XIAOSA
		y_save_tuple_execution_num();
#endif
		cull_queue(); //每次都约简测试用例,约简的对象是最优化测试用例(最优化测试用例什么时候改变的?)

		if (!queue_cur)
		{ //每轮询完一次所有测试用例,就进入一次

#ifdef XIAOSA
			y_save_information_big_cycle(); //save the information in each big cycle
#endif
			queue_cycle++; //记录循环次数
			current_entry = 0;
			cur_skipped_paths = 0;
			queue_cur = queue; //选择一个测试用例

			while (seek_to)
			{ //这里是用来恢复fuzz的
				current_entry++;
				seek_to--;
				queue_cur = queue_cur->next;
			}

			show_stats(); //显示

			if (not_on_tty)
			{
				ACTF("Entering queue cycle %llu.",queue_cycle);
				fflush(stdout); //立刻输出
			}

			/* If we had a full queue cycle with no new finds, try
			 recombination strategies next. */

			if (queued_paths == prev_queued)
			{ //第一次prev_queued为0,queued_paths是queue中的数量

				if (use_splicing)
					cycles_wo_finds++;
				else
					use_splicing = 1;
			}
			else
				cycles_wo_finds = 0;

			prev_queued = queued_paths;

			if (sync_id && queue_cycle == 1 && getenv("AFL_IMPORT_FIRST"))
				sync_fuzzers(use_argv);
		}
		//qemu模式下 use_argv afl-qemu-trace -- afl-qemu-out .cur_input
#ifdef XIAOSA
		fuzz_start_us = get_cur_time();
#endif
		skipped_fuzz = fuzz_one(use_argv); //从此正式开始fuzz.运行一次后 跑的快的肯定是被约简过的

#ifdef XIAOSA
		fuzz_stop_us = get_cur_time();
		queue_cur->fuzz_one_time=alloc_printf( "%s",DTD(fuzz_stop_us,fuzz_start_us));
		y_save_fuzzone_end_each_cycle();
#endif

		if (!stop_soon && sync_id && !skipped_fuzz)
		{

			if (!(sync_interval_cnt++ % SYNC_INTERVAL))
				sync_fuzzers(use_argv); //从其他fuzzer中获取testcase.并测试

		}

		if (stop_soon)
			break;

		queue_cur = queue_cur->next; //下一个queue中的测试用例
		current_entry++;

	}

	if (queue_cur)
		show_stats();

	write_bitmap(); //保存trace_bit
	write_stats_file(0,0);
	save_auto();

	stop_fuzzing:

	SAYF(CURSOR_SHOW cLRD "\n\n+++ Testing %s +++\n" cRST,
			stop_soon == 2 ?
					"ended via AFL_EXIT_WHEN_DONE" : "aborted by user");

	/* Running for more than 30 minutes but still doing first cycle? */

	if (queue_cycle == 1 && get_cur_time() - start_time > 30 * 60 * 1000)
	{

		SAYF(
				"\n" cYEL "[!] " cRST "Stopped during the first cycle, results may be incomplete.\n" "    (For info on resuming, see %s/README.)\n",
				doc_path);

	}

	fclose(plot_file);
	destroy_queue();
	destroy_extras();
	ck_free(target_path);

	alloc_report();

	OKF("We're done here. Have a nice day!\n");
	/* add the "}" in the last place of the file of /tmp/trace */
#ifdef XIAOSA

	tmpy = alloc_printf("%s/test_add.plot",out_dir);
	fdy = open(tmpy,O_WRONLY | O_CREAT | O_APPEND,0600); //需要追加的模式
	if (fdy < 0)
		PFATAL("Unable to create '%s'","/tmp/trace");
	ck_free(tmpy);

	tmpy = alloc_printf("}\n");
	ck_write(fdy,tmpy,strlen(tmpy),"%s/test_add.plot");
	ck_free(tmpy);

	close(fdy);
#endif

	exit(0);

}




