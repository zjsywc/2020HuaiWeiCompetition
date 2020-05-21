/*
 * @Description:
 * @Version: 2.0
 * @Autor: Seven
 * @Date: 2020-04-04 20:16:09
 * @LastEditors: Seven
 * @LastEditTime: 2020-04-26 23:18:58
 */

#define LINUX     // 用于区分在Linux和Windows运行时所需的头文件。
//#define TESTTIME  // 用于控制函数是否测试运行时间。
//#define TESTLOCAL // 控制本地测试使用哪些文件，控制线上测试使用哪些文件。

#include <iostream>
#include <vector>
#include <sstream>
#include <fstream>
#include <cmath>
#include <cstdlib>
#include <time.h>
#include <iomanip>
#ifdef LINUX
#include <unistd.h>
#endif
#include <iterator>
#ifdef LINUX
#include <pthread.h>
#endif
#include "stdio.h"
#include "string.h"
#include <assert.h>
#include <fcntl.h>
#ifdef LINUX
#include <sys/mman.h>
#endif
#include <sys/stat.h>
#include <sys/types.h>
#include <stdlib.h>
#ifdef LINUX
#include <sys/time.h>
#endif
#include <ctime>
#include <map>
#include <algorithm>
#include <queue>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <string>
#include <time.h>
#include <climits>

#include <mutex>

using namespace std;

#define CICLE_LEN 8 //头尾相接需要加1
#define MAX_VERTEX_SIZE 55000 //原280000

//有向图求环
//使用矩阵,需要优化
//使用边集数组优化时间复杂度
//使用广度优先搜索优化有向图两点之间所有路径
//防止非连通图的情况
//DAG+BFS+distance减枝,快乐0.7倍
//Hashset优化遍历,9万数据快乐7倍
//java写好改写的C++,痛苦10倍
//优化拷贝构造,pop()
//优化new delete
//优化std::pair
//使用数组优化 unordered_map 从55S降到20S
//双向BFS进行优化
//优化不访问比当前节点小的节点
//使用visited数组优化每次都会创建unordered_map
//7层变成3层加2层
//优化多线程的任务分配
//enumMap.insert(map<int, CString> :: value_type(2, "Two"))

//解决默认无法hash vector
//2020.4.8:为MMAP写方式，加入多线程。
//2020.4.11: 使用hopman_fast实现int2char。
//2020.4.11: 对hopman_fast实现多线程。
//2020.4.11: 删除msync，该函数在鲲鹏服务器上费时间，且删除后不影响内容写入到文件。
//2020.4.11: 在向虚拟内存拷贝前，不再拼接字符串，而是分组的、多线程的向虚拟内存区拷贝。
//优化点:
//1.改成dfs加三层for循环,三层for循搜索反向剪枝,dfs实现5+2
//2.使用多线程进行读文件
//3.去掉拓扑排序
//4.通过建表的方式优化IO
//5.修改分组数和线程数
//6.去掉多余内存拷贝,和生成
//7.计数排序优化建图和做映射
//8.使用分组的标记的方法优化排序过程
//9.使用多线程转换inttochar

// 用于将int转char。
namespace hopman_fast
{
struct itostr_helper
{
    static unsigned out[10000];

    itostr_helper()
    {
        for (int i = 0; i < 10000; i++)
        {
            unsigned v = i;
            char *o = (char *)(out + i);
            o[3] = v % 10 + '0';
            o[2] = (v % 100) / 10 + '0';
            o[1] = static_cast<char>((v % 1000) / 100) + '0';
            o[0] = static_cast<char>((v % 10000) / 1000);
            if (o[0])
                o[0] |= 0x30;
            else if (o[1] != '0')
                o[0] |= 0x20;
            else if (o[2] != '0')
                o[0] |= 0x10;
            else
                o[0] |= 0x00;
        }
    }
};

unsigned itostr_helper::out[10000];

itostr_helper hlp_init;

template <typename T>
void itostr(T o, std::string &out)
{
    typedef itostr_helper hlp;

    unsigned blocks[3], *b = blocks + 2;
    blocks[0] = o < 0 ? ~o + 1 : o;
    blocks[2] = blocks[0] % 10000;
    blocks[0] /= 10000;
    blocks[2] = hlp::out[blocks[2]];

    if (blocks[0])
    {
        blocks[1] = blocks[0] % 10000;
        blocks[0] /= 10000;
        blocks[1] = hlp::out[blocks[1]];
        blocks[2] |= 0x30303030;
        b--;
    }

    if (blocks[0])
    {
        blocks[0] = hlp::out[blocks[0] % 10000];
        blocks[1] |= 0x30303030;
        b--;
    }

    char *f = ((char *)b);
    f += 3 - (*f >> 4);

    char *str = (char *)blocks;
    if (o < 0)
        *--f = '-';
    out.assign(f, (str + 12) - f);
}

template <typename T>
std::string itostr(T o)
{
    std::string result;
    itostr(o, result);
    return result;
}
} // namespace hopman_fast

// 用于指示，如何分段读取虚拟内存空间。
struct ReadFileInfo
{
    char *map;
    int thread; // 指明是哪个线程存储空间。
    int start;  // 指明区段的起始位置，注意包括该位置。
    int end;    // 指明区段的终止位置，注意不包括该位置。
};

// 用于记录当前已经有哪些线程id被用，以此指示某个线程应该获得哪个线程id。
struct GroupThreadID
{
    int total; // 表示总共有几个线程。
    int cur;   // 表示当前位于哪一线程id还没被用过。
};

// 用于记录当前已经有哪些数据组被处理，以此指示某个线程应该去处理哪个数据组。
struct GroupVertex
{
    int total;         // 表示组数总共有几组。
    int cur;           // 表示当前位于哪一数据组还没被处理过。
    vector<int> start; // 表示某一数据组的起始位置，包括该位置。
    vector<int> end;   // 表示某一数据组的终止位置，不包括该位置。
};

// 用于指示，某个组的某个路径长度的路径存放在哪个线程存储空间的哪个路径长度的哪个区段[)。
struct CycleStoreInfo
{
    int thread; // 指明是哪个线程存储空间。
    int start;  // 指明区段的起始位置，注意包括该位置。
    int end;    // 指明区段的终止位置，注意不包括该位置。
};

// 用于存储拷贝信息。
struct CopyInfo
{
    int total;          // 表示组数总共有几组。
    int cur;            // 表示当前位于哪一组。
    vector<char *> map; // 用于存储拷贝的目标地址。
    vector<char *> str; // 用于存储待拷贝字符串的首地址。
    vector<int> size;   // 用于存储待拷贝字符串的大小。
};
//建图
int adjacencyDirectionMap[MAX_VERTEX_SIZE][50];        //有向邻接表
int adjacencyReverseDirectionMap[MAX_VERTEX_SIZE][50]; //反向邻接表
int adjPos[MAX_VERTEX_SIZE] = {0};
int adjRPos[MAX_VERTEX_SIZE] = {0};

//方便多线程均匀
int vectorArrayForSolveProble[MAX_VERTEX_SIZE]; // 用于存储入度和出度均不为0的顶点，以便多线程的任务均匀。
int vectorArrayPosForSolveProble = 0;           // 用于指示入度和出度均不为0的顶点数量。

int indegreesMap[MAX_VERTEX_SIZE];  //入度表
int outdegreesMap[MAX_VERTEX_SIZE]; //出度表

//计数排序的痛
int arr[MAX_VERTEX_SIZE] = {0};
int mapVirtualId[MAX_VERTEX_SIZE];
int mapRealId[MAX_VERTEX_SIZE];
//图
class Graph
{
public:
    // 多线程。
    static const int threadNum = 6;               // 定义线程数。
    GroupThreadID groupThreadID = {threadNum, 0}; // 用于给线程分配线程id。
    mutex mtx;                                    // 互斥锁。
    // * readfile-多线程。
    ReadFileInfo readFileInfo[threadNum]; // 用于记录每个线程应该处理的范围，并指定存储的空间。
    // * solveproblem-多线程。
    static const int cycleMinLen = 3;                              // 环的最短长度为3。
    static const int cycleMaxLen = 7;                              // 环的最长长度为7。
    static const int cycleLenType = cycleMaxLen - cycleMinLen + 1; // 环的路径长度有5种，分别为3，4，5，6，7。
    static const int groupVertexNum = 256;                          // 顶点最多可以分为几组，这个参数可调。
    GroupVertex groupVertex;                                       // 用于记录当前已经有哪些数据组被处理，以此指示某个线程应该去处理哪个数据组。
    vector<int> ans[threadNum][cycleLenType];                      // 一个二维数组，第一维表示线程存储空间，第二维表示某个线程的ans3-ans7的向量。
    int pos[threadNum][cycleLenType];                              // 一个二维数组，第一维表示线程存储空间，第二维表示某个线程的某个ans的当前位置。
    CycleStoreInfo cycleStoreInfo[groupVertexNum][cycleLenType];   // 记录相应数据组的某个路径长度的路径被存放在哪里。
    // * tostring-多线程。
    vector<char> stringCycle[groupVertexNum][cycleLenType]; // 用于存储分类转换好的数据。
    int stringCyclePos[groupVertexNum][cycleLenType];
    // * copystring-多线程。
    CopyInfo copyInfo; // 用于存储预先设置好的map地址。

    // int *mapVirtualId; //虚拟映射
    // int *mapRealId;    //真实映射

    int vertexSize = 0;     //顶点个数
    int userVertexSize = 0; //有用的顶点个数

    vector<int> graphVertexList; //顶点集合
    vector<int> inputList;
    int inputListSize = 0;
    vector<int> inputListSub[threadNum];
    int inputListSubSize[threadNum] = {0};

public:
    Graph();
    // 读文件操作相关函数。
    void char2int(int *input, int *pos, char *p);
    void readFile(string fileName);
    void readFileMMAP(char *map, int &start, int &end, int &threadID); //mmap读文件
    void readFileMMAPParallel(string fileName, void *g);
    // 写文件操作相关函数。
    void toString(const int &groupNum);                  // 单线程int转str。
    void toStringParallel(Graph *g);                     // 多线程int转str。
    void copyStrParallel(char *map, string &allStr);     // 多线程拷贝string到虚拟内存。
    void copyString(char *map, char *str, int size);     // 单线程的拷贝字符串至虚拟内存区。
    void copyStringParallel(char *map, Graph *g);        // 多线程的拷贝字符串至虚拟内存区。
    void writeFileMMAP(string resultFileName, Graph *g); // MMAP写文件。
    void writeFileMMAPByArray(string resultFileName, Graph *g);
    // 找环操作相关函数。
    void excuteMap();  //构造虚拟和真实映射表
    void buildGraph(); //建图
    void dag();        //拓扑排序
    void solveProblemByArray(int start, int end, int threadID);
    void dfsfindFrontNode(int head, int cur, int level, int pathFront[], int pathSize, bool visitedFront[], char distance[], int threadID);
    void solveProblemByArrayParallel(Graph *g);
    void addResultByArray(int frontList[], int &pathFrontSize, int front, int front2, int &threadID);
    void CountSort(vector<int> &v);
    void CountSortAndCopy(vector<int> input[], vector<int> &graphList);
};

Graph::Graph()
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    inputList.reserve(600000);
    for (int i = 0; i < threadNum; i++)
        inputListSub[i].reserve(600000);

    // 为存储路径动态分配空间，并初始化。（数组长度由大佬实验得到，若一个int占4字节，则一个空间约151.4MB。）
    for (int i = 0; i < threadNum; i++)
    {
        ans[i][0].reserve(3 * 500000);
        ans[i][1].reserve(4 * 500000);
        ans[i][2].reserve(5 * 1000000);
        ans[i][3].reserve(6 * 2000000);
        ans[i][4].reserve(7 * 3000000);
    }

    // 初始化用于指示位置的变量。
    for (int i = 0; i < threadNum; i++)
        for (int j = 0; j < cycleLenType; j++)
            pos[i][j] = 0;

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function Graph time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}
// 用于将int转char。
const char digit_pairs[201] =
    {
        "00010203040506070809"
        "10111213141516171819"
        "20212223242526272829"
        "30313233343536373839"
        "40414243444546474849"
        "50515253545556575859"
        "60616263646566676869"
        "70717273747576777879"
        "80818283848586878889"
        "90919293949596979899"};

void itostr(unsigned val, char *s, int &size)
{

    if (val == 0)
    {
        size = 0;
        s[size++] = '0';
        return;
    }

    if (val >= 10000)
    {
        if (val >= 10000000)
        {
            if (val >= 1000000000)
                size = 10;
            else if (val >= 100000000)
                size = 9;
            else
                size = 8;
        }
        else
        {
            if (val >= 1000000)
                size = 7;
            else if (val >= 100000)
                size = 6;
            else
                size = 5;
        }
    }
    else
    {
        if (val >= 100)
        {
            if (val >= 1000)
                size = 4;
            else
                size = 3;
        }
        else
        {
            if (val >= 10)
                size = 2;
            else
                size = 1;
        }
    }
    char *c = s + size - 1;
    while (val >= 100)
    {
        int pos = val % 100;
        val /= 100;
        *(short *)(c - 1) = *(short *)(digit_pairs + 2 * pos);
        c -= 2;
    }
    while (val > 0)
    {
        *c-- = '0' + (val % 10);
        val /= 10;
    }
    return;
}

//MMAP方式读文件
void Graph::readFile(string fileName)
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // 确定文件大小。
    int fd = open(fileName.c_str(), O_RDONLY);
    struct stat fileState;
    fstat(fd, &fileState);
    int fileSize = fileState.st_size;

    // 进行内存映射。
    char *map = (char *)mmap(0, fileSize, PROT_READ, MAP_SHARED, fd, 0);
    if (map == MAP_FAILED)
    {
        close(fd);
        perror("Error mmapping the file");
        exit(EXIT_FAILURE);
    }

    // 处理。
    int i = 0;
    while (i < fileSize)
    {
        char2int(&inputList[0], &inputListSize, map + i); // 逐行的转换。
        while (map[i++] != '\n')                          // 确定下一行的起始位置。
            ;
    }

    if (munmap(map, fileSize) == -1) // 解除内存映射。
    {
        close(fd);
        perror("Error un-mmapping the file");
        exit(EXIT_FAILURE);
    }

    // 关闭文件。
    close(fd);

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function readFileMMAP time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

void Graph::readFileMMAP(char *map, int &start, int &end, int &threadID)
{
    for (int i = start; i < end;)
    {
        char2int(&inputListSub[threadID][0], &inputListSubSize[threadID], map + i); // 逐行的转换。
        while (map[i++] != '\n')                                                    // 确定下一行的起始位置。
            ;
    }
}

void *thread4ReadFileMMAP(void *ptr)
{
    Graph *g = (Graph *)ptr;

    // 明确该线程的id。
    int threadID = 0;

    g->mtx.lock(); // 等待其它线程解除占用。
    if (g->groupThreadID.cur >= g->groupThreadID.total)
    {
        g->mtx.unlock(); // 解除占用。
        return nullptr;  // 线程id已用完，因此不允许再开新的线程。
    }
    threadID = g->groupThreadID.cur++; // 获得线程id。
    g->mtx.unlock();                   // 解除占用。

    // 处理。
    char *map = g->readFileInfo[threadID].map;
    int start = g->readFileInfo[threadID].start; // 获得该数据组的待处理数据的起始位置。
    int end = g->readFileInfo[threadID].end;     // 获得该数据组的待处理数据的终止位置。

    g->readFileMMAP(map, start, end, threadID); // 开始处理该组数据。
}

void Graph::readFileMMAPParallel(string fileName, void *g)
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // 确定文件大小。
    int fd = open(fileName.c_str(), O_RDONLY);
    struct stat fileState;
    fstat(fd, &fileState);
    int fileSize = fileState.st_size;

    // 进行内存映射。
    char *map = (char *)mmap(0, fileSize, PROT_READ, MAP_SHARED, fd, 0);
    if (map == MAP_FAILED)
    {
        close(fd);
        perror("Error mmapping the file");
        exit(EXIT_FAILURE);
    }

    // 处理。
    // 分组。
    for (int i = 0; i < threadNum; i++)
    {
        readFileInfo[i].map = map;
        readFileInfo[i].thread = i;
    }

    int range = fileSize / threadNum + 1;
    int i = 0;
    readFileInfo[i].start = 0;
    while (i < threadNum - 1)
    {
        readFileInfo[i].end = readFileInfo[i].start + range;
        while (map[readFileInfo[i].end++] != '\n')
            ; // 找到换行符后的那个位置。
        readFileInfo[i + 1].start = readFileInfo[i].end;
        i++;
    }
    readFileInfo[i].end = fileSize;

    groupThreadID.cur = 0; // 将线程id置零。

    // 开多线程。
    int rc[threadNum];
    pthread_t threads[threadNum];
    pthread_attr_t attr;
    void *status;

    // Initialize and set thread joinable
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_create(&threads[i], &attr, thread4ReadFileMMAP, (void *)g);

    // free attribute and wait for the other threads
    pthread_attr_destroy(&attr);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_join(threads[i], &status);

    if (munmap(map, fileSize) == -1) // 解除内存映射。
    {
        close(fd);
        perror("Error un-mmapping the file");
        exit(EXIT_FAILURE);
    }

    // 关闭文件。
    close(fd);

    // 这里是暂时的。
    // for (int i = 0; i < threadNum; i++)
    //     for (int j = 0; j < inputListSubSize[i]; j++)
    //         inputList[inputListSize++] = inputListSub[i][j];

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function readFileMMAP time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

//单线程的int转string。
void Graph::toString(const int &groupNum)
{
    // 逐条的转换所有环。
    int size;
    int curLen = 0;
    for (int cycleLen = cycleMinLen; cycleLen <= cycleMaxLen; cycleLen++) // 逐个长度的添加路径。
    {
        curLen = cycleLen - cycleMinLen;
        // 开辟空间。
        int pathNum = (cycleStoreInfo[groupNum][curLen].end - cycleStoreInfo[groupNum][curLen].start) / cycleLen; // 确定某个路径长度的路径数量。
        const int maxCharPer = 11;                                                                                // 因为31位能表示的数值最多占10个字符，而每个数值后面，
        int size = maxCharPer * cycleLen * pathNum;                                                               // 确定最大的所需的空间。
        stringCycle[groupNum][curLen].reserve(size);
        stringCyclePos[groupNum][curLen] = 0;
        // 转换。
        for (int j = cycleStoreInfo[groupNum][curLen].start, k = 1; j < cycleStoreInfo[groupNum][curLen].end; j++, k++) // 逐个处理这条路径上的结点。
        {
            int tmpPos = cycleStoreInfo[groupNum][curLen].thread;
            int tmpVal = ans[tmpPos][curLen][j];
            itostr(tmpVal, &stringCycle[groupNum][curLen][stringCyclePos[groupNum][curLen]], size);
            stringCyclePos[groupNum][curLen] += size;
            stringCycle[groupNum][curLen][stringCyclePos[groupNum][curLen]++] = (k >= cycleLen) ? '\n' : ',';
            k = (k >= cycleLen) ? 0 : k;
        }
    }
}

// 线程
void *thread4ToString(void *ptr)
{
    Graph *g = (Graph *)ptr;

    while (1)
    {
        g->mtx.lock();                                  // 等待其它线程解除占用。
        if (g->groupVertex.cur >= g->groupVertex.total) // 若已经处理完所有数据，则终止线程。
        {
            g->mtx.unlock(); // 解除占用。
            return nullptr;
        }
        int groupNum = g->groupVertex.cur++; // 获得待处理的数据组。
        g->mtx.unlock();                     // 解除占用。

        g->toString(groupNum); // 开始处理数据。
    }
}

// 多线程的int转string。
void Graph::toStringParallel(Graph *g)
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // 分组；
    groupVertex.cur = 0;
    groupVertex.total = groupVertexNum;

    // 开多线程。
    int rc[threadNum];
    pthread_t threads[threadNum];
    pthread_attr_t attr;
    void *status;

    // Initialize and set thread joinable
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_create(&threads[i], &attr, thread4ToString, (void *)g);

    // free attribute and wait for the other threads
    pthread_attr_destroy(&attr);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_join(threads[i], &status);

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function toStringParallel time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

//单线程的拷贝。
void Graph::copyString(char *map, char *str, int size)
{
    // 拷贝存储在str中的环到虚拟内存的相应区域。
    memcpy(map, str, size);
}

// 线程，拷贝string到虚拟内存。
void *thread4CopyString(void *ptr)
{
    Graph *g = (Graph *)ptr;

    while (1)
    {
        g->mtx.lock();                            // 等待其它线程解除占用。
        if (g->copyInfo.cur >= g->copyInfo.total) // 若已经处理完所有数据，则终止线程。
        {
            g->mtx.unlock(); // 解除占用。
            return nullptr;
        }
        int groupNum = g->copyInfo.cur++; // 获得待处理的数据组。
        g->mtx.unlock();                  // 解除占用。

        char *map = g->copyInfo.map[groupNum]; // 获得虚拟内存区的起始位置。
        char *str = g->copyInfo.str[groupNum]; // 获得待写入字符串的起始位置。
        int size = g->copyInfo.size[groupNum]; // 获得待写入字符串的大小。

        g->copyString(map, str, size); // 开始处理数据。
    }
}

// 多线程的拷贝数据到虚拟内存。
void Graph::copyStringParallel(char *map, Graph *g)
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // 分组。
    copyInfo.cur = 0;
    copyInfo.total = groupVertexNum * cycleLenType;
    copyInfo.map.resize(copyInfo.total);  // 预先分配空间。
    copyInfo.str.resize(copyInfo.total);  // 预先分配空间。
    copyInfo.size.resize(copyInfo.total); // 预先分配空间。

    int groupNum = 0;
    int cycleLen = 0;
    for (int i = 0; i < copyInfo.total; i++) // 确定好每组要拷贝到虚拟内存中的首地址。
    {
        copyInfo.map[i] = map;                                 // 获得虚拟内存区的起始位置。
        copyInfo.str[i] = &stringCycle[groupNum][cycleLen][0]; // 获得待写入字符串的起始位置。
        copyInfo.size[i] = stringCyclePos[groupNum][cycleLen]; // 获得待写入字符串的大小。
        map += stringCyclePos[groupNum][cycleLen];             // 重新计算虚拟内存区中的下个起始位置。

        groupNum++;                     // 组号加一。
        if (groupNum >= groupVertexNum) // 如果组号已经大于等于极限。
        {
            groupNum = 0; // 组号清零。
            cycleLen++;   // 路径长度加一。
        }
    }

    // 开多线程。
    int rc[threadNum];
    pthread_t threads[threadNum];
    pthread_attr_t attr;
    void *status;

    // Initialize and set thread joinable
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_create(&threads[i], &attr, thread4CopyString, (void *)g);

    // free attribute and wait for the other threads
    pthread_attr_destroy(&attr);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_join(threads[i], &status);

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function copyStrParallel time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

//MMAP写文件
void Graph::writeFileMMAPByArray(string resultFileName, Graph *g)
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // 将int数据转换到一个string中。
    string allstring;
    string tmp;
    // 添加路径总数。
    int cycleNum = 0;
    for (int i = 0; i < threadNum; i++)
        cycleNum += (pos[i][0] / 3 + pos[i][1] / 4 + pos[i][2] / 5 + pos[i][3] / 6 + pos[i][4] / 7);
    hopman_fast::itostr(cycleNum, tmp);
    allstring += tmp;
    allstring += '\n';

    // 将所有路径转换成char。
    toStringParallel(g);

    // 计算文件大小。
    size_t textSize = allstring.size();
    for (int cycleLen = cycleMinLen; cycleLen <= cycleMaxLen; cycleLen++) // 逐个长度的添加路径。
        for (int i = 0; i < groupVertexNum; i++)                          // 逐个组的处理。
            textSize += stringCyclePos[i][cycleLen - cycleMinLen];

    // 打开一个文件。
    int fd = open(resultFileName.c_str(), O_RDWR | O_CREAT, 0666);
    if (fd == -1)
    {
        perror("Error opening file for writing");
        exit(EXIT_FAILURE);
    }

    // 定位到文件尾。
    if (lseek(fd, textSize - 1, SEEK_SET) == -1)
    {
        close(fd);
        perror("Error calling lseek() to 'stretch' the file");
        exit(EXIT_FAILURE);
    }
    // 在文件末写入一个结束符。
    if (write(fd, "", 1) == -1)
    {
        close(fd);
        perror("Error writing last byte of the file");
        exit(EXIT_FAILURE);
    }

    // 定位到文件头。
    lseek(fd, 0, SEEK_SET);
    // 进行MMAP映射。
    char *map = (char *)mmap(NULL, textSize, PROT_WRITE, MAP_SHARED, fd, 0);
    if (map == MAP_FAILED)
    {
        close(fd);
        perror("Error mmapping the file");
        exit(EXIT_FAILURE);
    }

    // 拷贝数据到虚拟内存区。
    char *p = map;
    copyString(p, &allstring[0], allstring.size());
    p += allstring.size();

    copyStringParallel(p, g);

    // 解除映射。
    if (munmap(map, textSize) == -1)
    {
        close(fd);
        perror("Error un-mmapping the file");
        exit(EXIT_FAILURE);
    }

    // 关闭文件。
    close(fd);

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function writeFileMMAP time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

// 该函数只能将char转uint32_t。
void Graph::char2int(int *input, int *pos, char *p)
{
    // 处理第1个数。
    input[*pos] = 0;
    while (*p >= '0' && *p <= '9')
    {
        input[*pos] = (input[*pos] * 10) + (*p - '0');
        ++p;
    }
    if (input[*pos] <= 50000) // 只有顶点ID大于50000才写入inputList。
        ++(*pos);
    else
        return;

    ++p; // 跳过逗号。

    // 处理第2个数。
    input[*pos] = 0;
    while (*p >= '0' && *p <= '9')
    {
        input[*pos] = (input[*pos] * 10) + (*p - '0');
        ++p;
    }
    if (input[*pos] <= 50000) // 只有顶点ID大于50000才写入inputList。
    {
        ++(*pos);
    }
    else
    {
        --(*pos);
        return;
    }

    ++p; // 跳过逗号。

    // 处理第3个数。在初赛中第3个数可以不处理，但p要走完。
    //weight = 0;
    /*  // 初赛中不需要处理。
        while (*p >= '0' && *p <= '9')
        {
            weight = (weight * 10) + (*p - '0');
            ++p;
        }
    */
}

void Graph::buildGraph()
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // indegreesMap.reserve(vertexSize);
    // memset(&indegreesMap[0], 0, sizeof(int) * vertexSize);
    // outdegreesMap.reserve(vertexSize);
    // memset(&outdegreesMap[0], 0, sizeof(int) * vertexSize);

    //for (int i = 0; i < inputList.size(); i += 2)
    for (int nt = 0; nt < threadNum; nt++)
    {
        for (int i = 0; i < inputListSubSize[nt]; i += 2)
        {
            int start = mapVirtualId[inputListSub[nt][i]];
            int end = mapVirtualId[inputListSub[nt][i + 1]];
            adjacencyDirectionMap[start][adjPos[start]++] = end;
            adjacencyReverseDirectionMap[end][adjRPos[end]++] = start;
            ++indegreesMap[end];
            ++outdegreesMap[start];
        }
    }
    for (int i = 0; i < MAX_VERTEX_SIZE; i++)
    {
        if (adjPos[i] != 0)
            sort(adjacencyDirectionMap[i], adjacencyDirectionMap[i] + adjPos[i]);
        if (adjRPos[i] != 0)
            sort(adjacencyReverseDirectionMap[i], adjacencyReverseDirectionMap[i] + adjRPos[i]);
    }

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function buildGraph time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

//拓扑排序
void Graph::dag()
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    userVertexSize = vertexSize; //能构成环的顶点
    //BFS用的队列
    queue<int> queue;
    //确定入度为0的点
    for (auto &elem : graphVertexList)
    {

        if (indegreesMap[mapVirtualId[elem]] == 0)
        {
            /* code */
            queue.push(mapVirtualId[elem]);
        }
        // else if (outdegreesMap[mapVirtualId[elem]] == 0)
        // {
        //     /* code */
        //     queue.push(mapVirtualId[elem]);
        // }
    }
    //bfs进行排序
    while (!queue.empty())
    {
        /* code */
        int pre = queue.front();
        queue.pop();
        userVertexSize--;
        //如果存在
        if (indegreesMap[pre] == 0)
        {
            for (int i = 0; i < adjPos[pre]; i++)
            {
                int cur = adjacencyDirectionMap[pre][i];
                if (--indegreesMap[cur] == 0)
                    queue.push(cur);
            }
        }
        // if (outdegreesMap[pre] == 0)
        // {
        //     for (int i = 0; i < adjRPos[pre]; i++)
        //     {
        //         int cur = adjacencyReverseDirectionMap[pre][i];
        //         if (--outdegreesMap[cur] == 0 && indegreesMap[cur] != 0)
        //             queue.push(cur);
        //     }
        // }
    }

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function dag time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}
//构造虚拟和真实映射表
void Graph::excuteMap()
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    graphVertexList.reserve(600000);
    // graphVertexList = inputList;
    //sort(graphVertexList.begin(), graphVertexList.end());
    // CountSort(graphVertexList);
    CountSortAndCopy(inputListSub, graphVertexList);
    // graphVertexList.erase(unique(graphVertexList.begin(), graphVertexList.end()), graphVertexList.end());

    //获取长度
    vertexSize = graphVertexList.size();
    //构建映射表
    // mapRealId = new int[vertexSize];
    // mapVirtualId = new int[maxVertexOrder + 1];
    //对所有顶点做映射
    int j = 0;

    for (auto &n : graphVertexList)
    {
        /* code */
        mapRealId[j] = n;
        mapVirtualId[n] = j;
        j++;
    }

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function excuteMap time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}
//比较
bool cmpBack(const vector<int> &a, const vector<int> &b)
{
    if (a.size() == b.size())
    {
        for (int i = a.size() - 1; i >= 0; i--)
        {
            if (a[i] == b[i])
                continue;

            return a[i] < b[i];
        }
    }

    return a.size() < b.size();
}

//找环。
void Graph::solveProblemByArray(int start, int end, int threadID)
{
    const int visitedSize = vertexSize; // 顶点表中顶点的数量。
    queue<int> backer;                  // 用于存储待处理的反向路径的队列。
    int pathFront[7] = {0};
    // bool visitedBack[visitedSize] = {false}; // 用于标记在反向搜索中，某顶点是否被访问过。
    char distance[vertexSize] = {10};
    bool visitedFront[visitedSize] = {false};
    for (int i = start; i < end; i++) // 逐个顶点的搜索以该顶点为起点的路径。
    {
        int head = vectorArrayForSolveProble[i]; // 从数组中拿出要处理的顶点。

        // if (indegreesMap[head] == 0) // 如果该顶点的入度为0，即该顶点不可能构成环，因此不用再寻找以它为顶点的路径。
        //     continue;
        for (int k = head + 1; k < vertexSize; k++)
            distance[k] = 10;
        // BFS搜索反向三层内的所有点的所有路径。耗时0.8s
        int back1 = 0;
        int back2 = 0;
        int back3 = 0;
        distance[head] = 0;
        for (int i1 = 0; i1 < adjRPos[head]; i1++)
        {
            back1 = adjacencyReverseDirectionMap[head][i1];
            if (back1 <= head)
                continue;
            distance[back1] = 1;
            for (int i2 = 0; i2 < adjRPos[back1]; i2++)
            {
                back2 = adjacencyReverseDirectionMap[back1][i2];
                if (back2 <= head)
                    continue;
                if (distance[back2] > 2)
                    distance[back2] = 2;

                for (int i3 = 0; i3 < adjRPos[back2]; i3++)
                {
                    back3 = adjacencyReverseDirectionMap[back2][i3];
                    if (back3 <= head)
                        continue;
                    if (distance[back3] > 3)
                        distance[back3] = 3;
                }
            }
        }

        int pathSize = 0;
        //开始正向搜索
        dfsfindFrontNode(head, head, 0, pathFront, pathSize, visitedFront, distance, threadID);
    }
}

void Graph::dfsfindFrontNode(int head, int cur, int level, int pathFront[], int pathSize, bool visitedFront[], char distance[], int threadID)
{
    if (level > 6)
        return;

    visitedFront[cur] = true;
    pathFront[pathSize++] = cur;
    if (adjPos[cur] != 0)
    {
        for (int i = 0; i < adjPos[cur]; i++)
        {
            int front = adjacencyDirectionMap[cur][i];
            // //不存在该顶点
            if (indegreesMap[front] == 0)
                continue;
            //找比当前顶点大的点
            if (front < head)
                continue;
            if (level >= 3)
            {
                if (distance[front] > 3)
                    continue;
                if (pathSize + distance[front] > 7)
                    continue;
            }
            if (level > 1 && front == head)
                addResultByArray(pathFront, pathSize, -1, -1, threadID);
            if (level == 4 && !visitedFront[front])
            {
                if (adjPos[front] != 0)
                {
                    for (int j = 0; j < adjPos[front]; j++)
                    {
                        int front2 = adjacencyDirectionMap[front][j];
                        if (visitedFront[front2] && front2 != head)
                            continue;
                        if (front2 == head)
                        {
                            addResultByArray(pathFront, pathSize, front, -1, threadID);
                        }
                        else if (distance[front2] == 1)
                        {
                            addResultByArray(pathFront, pathSize, front, front2, threadID);
                        }
                    }
                }
            }
            if (level < 4)
            {
                if (!visitedFront[front])
                {
                    dfsfindFrontNode(head, front, level + 1, pathFront, pathSize, visitedFront, distance, threadID);
                }
            }
        }
    }
    visitedFront[cur] = false;
    pathSize--;
}

void *thread4SolveProblemByArray(void *ptr)
{
    Graph *g = (Graph *)ptr;

    // 明确该线程的id。
    int threadID = 0;

    g->mtx.lock(); // 等待其它线程解除占用。
    if (g->groupThreadID.cur >= g->groupThreadID.total)
    {
        g->mtx.unlock(); // 解除占用。
        return nullptr;  // 线程id已用完，因此不允许再开新的线程。
    }
    threadID = g->groupThreadID.cur++; // 获得线程id。
    g->mtx.unlock();                   // 解除占用。

    // 分组处理。
    while (1)
    {
        g->mtx.lock();                                  // 等待其它线程解除占用。
        if (g->groupVertex.cur >= g->groupVertex.total) // 直到处理完所有数据组才结束该线程。
        {
            g->mtx.unlock(); // 解除占用。
            return nullptr;
        }
        int groupNum = g->groupVertex.cur++; // 获得待处理数据组的组号。
        g->mtx.unlock();                     // 解除占用。

        int start = g->groupVertex.start[groupNum]; // 获得该数据组的待处理数据的起始位置。
        int end = g->groupVertex.end[groupNum];     // 获得该数据组的待处理数据的终止位置。

        for (int i = 0; i < g->cycleLenType; i++)
        {
            g->cycleStoreInfo[groupNum][i].thread = threadID;           // 记录该数据组的每个路径长度由哪个线程处理。
            g->cycleStoreInfo[groupNum][i].start = g->pos[threadID][i]; // 记录每个路径长度的起始位置。
        }

        g->solveProblemByArray(start, end, threadID); // 开始处理该组数据。

        for (int i = 0; i < g->cycleLenType; i++)
            g->cycleStoreInfo[groupNum][i].end = g->pos[threadID][i]; // 记录每个路径长度的终止位置。
    }
}

/**
  * @brief    多线程找环。
  * @param    g : 图相关信息。
  * @retval   无。
  */
void Graph::solveProblemByArrayParallel(Graph *g)
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

    // 过滤掉出度为0或入度为0的点。
    for (int i = 0; i < vertexSize; i++)
        if (indegreesMap[i] != 0 && outdegreesMap[i] != 0)
            vectorArrayForSolveProble[vectorArrayPosForSolveProble++] = i;

    // 平分顶点数。
    groupVertex.cur = 0;
    groupVertex.total = groupVertexNum;
    groupVertex.start.resize(groupVertexNum, 0);                   // 预先分配空间。
    groupVertex.end.resize(groupVertexNum, 0);                     // 预先分配空间。
    int range = vectorArrayPosForSolveProble / groupVertexNum + 1; // 确定每个组的处理范围。注意因为整数除法直接忽略小数，所以必须要加一，不然会漏掉部分。

    int k = 0;
    groupVertex.start[0] = 0;
    for (int i = range; i < vectorArrayPosForSolveProble; i += range)
    {
        groupVertex.end[k++] = i;
        groupVertex.start[k] = i;
    }
    groupVertex.end[k] = vectorArrayPosForSolveProble;

    groupThreadID.cur = 0; // 将线程id置零。

    // 开多线程。
    int rc[threadNum];
    pthread_t threads[threadNum];
    pthread_attr_t attr;
    void *status;

    // Initialize and set thread joinable
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_create(&threads[i], &attr, thread4SolveProblemByArray, (void *)g);

    // free attribute and wait for the other threads
    pthread_attr_destroy(&attr);

    for (int i = 0; i < threadNum; i++)
        rc[i] = pthread_join(threads[i], &status);

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function solveProblemByArrayParallel time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif
}

//添加结果。
void Graph::addResultByArray(int frontList[], int &pathFrontSize, int front, int front2, int &threadID)
{
    //为什么要缓存?
    // int pathResult[7] {0};
    // int pathSize = 0;

    // //添加前项路径
    // for (int i = 0; i < pathFrontSize; i++)
    // {
    //     pathResult[i] = mapRealId[frontList[i]];
    //     pathSize++;
    // }

    // if (front != -1)
    // {
    //     pathResult[pathSize++] = mapRealId[front];
    // }
    // if(front2!=-1){
    //     pathResult[pathSize++] = mapRealId[front2];
    // }
    // //添加结果
    // if (pathSize < 3 || pathSize > 7) // 如果路径长度不符合要求，则不添加。
    //     return;
    // for (int i = 0; i < pathSize; i++) //添加路径到相应位置。
    // {
    //     ans[threadID][pathSize - cycleMinLen][pos[threadID][pathSize - cycleMinLen]++] = pathResult[i];
    // }
    int pathSize = pathFrontSize;
    if (front != -1)
        pathSize++;
    if (front2 != -1)
        pathSize++;
    for (int i = 0; i < pathFrontSize; i++) //添加路径到相应位置。
    {
        ans[threadID][pathSize - cycleMinLen][pos[threadID][pathSize - cycleMinLen]++] = mapRealId[frontList[i]];
    }
    if (front != -1)
    {
        ans[threadID][pathSize - cycleMinLen][pos[threadID][pathSize - cycleMinLen]++] = mapRealId[front];
    }
    if (front2 != -1)
    {
        ans[threadID][pathSize - cycleMinLen][pos[threadID][pathSize - cycleMinLen]++] = mapRealId[front2];
    }
}
//计数排序
void Graph::CountSort(vector<int> &v)
{
    int index = 0;
    while (index < v.size())
    {
        arr[v[index]]++;

        ++index;
    }
    index = 0;
    for (int i = 0; i < MAX_VERTEX_SIZE; ++i)
    {
        while (arr[i]--)
        {
            v[index++] = i;
        }
    }
}
//计数排序加拷贝
void Graph::CountSortAndCopy(vector<int> input[], vector<int> &graphList)
{
    int index = 0;
    for (int i = 0; i < threadNum; i++)
    {
        index=0;
        while (index < inputListSubSize[i])
        {
            arr[input[i][index]]++;

            ++index;
        }
    }
    for (int i = 0; i < MAX_VERTEX_SIZE; ++i)
    {
        if (arr[i] != 0)
        {
            graphList.emplace_back(i);
        }
    }
}
//主函数
int main()
{
#ifdef TESTTIME // 用于计算程序运行总时间。
    struct timeval startTime, endTime;
    gettimeofday(&startTime, NULL);
#endif

#ifdef TESTLOCAL // 本地测试文件路径。
    string testFileName = "./data/test_data.txt";
    string resultFileName = "./projects/student/result.txt";
#else // 线上测试文件路径。
    string testFileName = "/data/test_data.txt";
    string resultFileName = "/projects/student/result.txt";
#endif

    Graph g;

    //g.readFile(testFileName);
    g.readFileMMAPParallel(testFileName, &g);

    g.excuteMap();
    g.buildGraph();
    //g.dag();
    g.solveProblemByArrayParallel(&g); // 多线程找环。

    g.writeFileMMAPByArray(resultFileName, &g);

#ifdef TESTTIME // 用于计算程序运行时间。
    gettimeofday(&endTime, NULL);
    double timeUse = (endTime.tv_sec - startTime.tv_sec) + (endTime.tv_usec - startTime.tv_usec) / 1000000.0;
    cout << "Function main time = " << timeUse << " s" << endl; //输出时间（单位：ｓ）
#endif

    exit(0); // 快速结束程序，释放资源。
    return 0;
}
