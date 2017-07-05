#include "distance.h"

//自定义排序
struct comp {
    bool operator ()(const DP& dpl, const DP& dpr) {
        return (dpl.distance >= dpr.distance); //这个是从大到小,距离一样
    }
};

//struct comp {
//    bool operator ()(const DP& dpl, const DP& dpr) {
//        return (dpl.distance >= dpr.distance);
//    }
//};

set<DP,comp> dis_list; // 记录所有的轨迹, 这个在c中没法调用 对于元素是自定义的结构体,还需要重写排序算法

u32 cal_distance_with_queue(struct queue_entry *queue,struct queue_entry *q)//q1 是最新的
{
	struct queue_entry *queue_cur = queue;
	double distance=0;
	while (queue_cur)
	{
		if ( queue_cur==q)
		{
			break;// the last is the self
		}
		distance=cal_two_input(queue_cur,q);//左边为旧,小号;右边是新,大号
		//生成一调新的记录
		DP tmp;
		tmp.distance=distance;
		tmp.fname_min=queue_cur->fname;
		tmp.fname_max=q->fname;
		dis_list.insert(tmp); //插入之后是有序的
		queue_cur = queue_cur->next;
	}
	//输出总的记录
//	update_distance_file(queue_cur->fname,q->fname,distance);
	update_distance_file();
	return 0;
}


//void update_distance_file(u8* fname_min, u8* fnamer_max, double distance)
void update_distance_file()
{
	//n个测试用例,就有n(n-1)/2次比较
	//输出文件定义
	fseek(distance_file,0,0);
	// 遍历 set
	for (auto it = dis_list.begin(), end = dis_list.end(); it != end; it++)
	{
		DP tmp = *it; //按照distance下的顺序进行
		fprintf(distance_file, "%s; %s; %0.f \n",
				tmp.fname_min, tmp.fname_max, tmp.distance); /* ignore errors */
		fflush(distance_file);
	}


}

void sort_distance(){
	//sort the vector of the distance of between all the inputs
}


