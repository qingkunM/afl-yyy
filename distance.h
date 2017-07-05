#ifndef DISTANCE_H
#define DISTANCE_H
//不能在头文件中做定义,否则会多次定义, 在头文件中只有声明

extern "C"{
#include "afl-distance.h" //这里申明的函数,在cpp中定义,在c中调用
}

#include <set>
#include <map>  //必须在cpp中

using namespace std;

double cal_two_input(struct queue_entry *ql,struct queue_entry *qr);


#endif
