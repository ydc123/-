#include <conio.h>
#include <atlstr.h>
#include <iostream>
#include "Point.h"
#include "Strategy.h"
#include <algorithm>
#include <ctime>
#include "Judge.h"
#include <map>
#include <vector>
#include <unordered_map>
#include <ctime>
#define maxn 12
#define maxm 8000000
#define P 131
#define mod 4194303
#define SZ(x) ((int)(x).size())
using namespace std;
typedef unsigned long long ULL;
const int me=2;
const int enemy=1;
const int WIN=2;
const int LOSE=1;
const int UNKNOWN=3;
struct Tree_Node
{
	Tree_Node *son[maxn];
	int n,w;
}Tree[maxm];
int nTree;
ULL Power[maxn*maxn];
int MonteCarlo(int y,int M,int N,int *top,int** board,int user_id);
ULL encode(int M,int N,int **board)
{
	ULL sum=0;
	for(int i=0;i<M;++i)
		for(int j=0;j<N;++j)
			sum=sum*P+board[i][j]+1;
	return sum;
}
int randint(int l,int r)
{
	return rand()%(r-l+1)+l;
}
int select(Tree_Node *rt,int M,int N,int *nowtop,int** board,int user_id,bool c=true,bool print=false)
{
	const int LEAST=2;
	double maxv,logn=log(rt->n+1);
	int y=-1;
	for(int k=0;k<N;++k)
		if(nowtop[k]>0)
		{
			pair<int,int> ans=rt->son[k]?make_pair(rt->son[k]->n,rt->son[k]->w):make_pair(0,0);
			if(ans.first<=LEAST)
				return k;
			double val=1.0*ans.second/ans.first;
			if(c)
				val+=2*sqrt(logn/ans.first);
			if(y==-1||maxv<val)
				y=k,maxv=val;
			if(print)
				_cprintf("(%d,%d) ",ans.first,ans.second);
		}
		else if(print)
			_cprintf("0 ");
	if(print)
		_cprintf("\n");
	return y;
}
Tree_Node* NewNode()
{
	Tree_Node *p=&Tree[++nTree];
	for(int i=0;i<maxn;++i)
		p->son[i]=0;
	p->n=p->w=0;
	return p;
}
int MonteCarlo(Tree_Node *rt,int y,int M,int N,int *top,int** board,int user_id,bool isRandom)
{
	static int can[maxn];
	int x=top[y]-1,val;
	board[x][y]=user_id;
	--top[y];
	if(x>0&&board[x-1][y]==3)
		--top[y];
	if(user_id==me&&machineWin(x,y,M,N,board))
		val=2;
	else if(user_id==enemy&&userWin(x,y,M,N,board))
		val=2;
	else
	{
		int n=0;
		bool nextRandom=isRandom;
		for(int i=0;i<N;++i)
			if(top[i]>0)
				can[++n]=i;
		if(n==0)
			val=0;
		else
		{
			int y;
			if(isRandom||rt->n==0)
				y=can[randint(1,n)],nextRandom=true;
			else
				y=select(rt,M,N,top,board,3-user_id);
			if(rt->son[y]==0)
				rt->son[y]=NewNode(),nextRandom=true;
			val=-MonteCarlo(rt->son[y],y,M,N,top,board,3-user_id,nextRandom);
		}
	}
	top[y]=x+1,board[x][y]=0;
	++rt->n,rt->w+=val;
	return val;
}
/*
	策略函数接口,该函数被对抗平台调用,每次传入当前状态,要求输出你的落子点,该落子点必须是一个符合游戏规则的落子点,不然对抗平台会直接认为你的程序有误
	
	input:
		为了防止对对抗平台维护的数据造成更改，所有传入的参数均为const属性
		M, N : 棋盘大小 M - 行数 N - 列数 均从0开始计， 左上角为坐标原点，行用x标记，列用y标记
		top : 当前棋盘每一列列顶的实际位置. e.g. 第i列为空,则_top[i] == M, 第i列已满,则_top[i] == 0
		_board : 棋盘的一维数组表示, 为了方便使用，在该函数刚开始处，我们已经将其转化为了二维数组board
				你只需直接使用board即可，左上角为坐标原点，数组从[0][0]开始计(不是[1][1])
				board[x][y]表示第x行、第y列的点(从0开始计)
				board[x][y] == 0/1/2 分别对应(x,y)处 无落子/有用户的子/有程序的子,不可落子点处的值也为0
		lastX, lastY : 对方上一次落子的位置, 你可能不需要该参数，也可能需要的不仅仅是对方一步的
				落子位置，这时你可以在自己的程序中记录对方连续多步的落子位置，这完全取决于你自己的策略
		noX, noY : 棋盘上的不可落子点(注:其实这里给出的top已经替你处理了不可落子点，也就是说如果某一步
				所落的子的上面恰是不可落子点，那么UI工程中的代码就已经将该列的top值又进行了一次减一操作，
				所以在你的代码中也可以根本不使用noX和noY这两个参数，完全认为top数组就是当前每列的顶部即可,
				当然如果你想使用lastX,lastY参数，有可能就要同时考虑noX和noY了)
		以上参数实际上包含了当前状态(M N _top _board)以及历史信息(lastX lastY),你要做的就是在这些信息下给出尽可能明智的落子点
	output:
		你的落子点Point
*/
extern "C" __declspec(dllexport) Point* getPoint(const int M, const int N, const int* top, const int* _board, 
	const int lastX, const int lastY, const int noX, const int noY){
	/*
		不要更改这段代码
	*/
	bool used=false;
	if(!used)
		AllocConsole(),used=true;
	double be=(double)clock()/CLOCKS_PER_SEC;
	int cntChess=0;
	int x = -1, y = -1;//最终将你的落子点存到x,y中
	int** board = new int*[M];
	Power[0]=1;
	for(int i=1;i<=N*M;++i)
		Power[i]=Power[i-1]*P;
	for(int i = 0; i < M; i++){
		board[i] = new int[N];
		for(int j = 0; j < N; j++){
			board[i][j] = _board[i * N + j];
			if(board[i][j]==2)
				++cntChess;
		}
	}
	board[noX][noY]=3;
	/*
		根据你自己的策略来返回落子点,也就是根据你的策略完成对x,y的赋值
		该部分对参数使用没有限制，为了方便实现，你可以定义自己新的类、.h文件、.cpp文件
	*/
	//Add your own code below
	
     //a naive example
	
	/*for (int i = N-1; i >= 0; i--) {
		if (top[i] > 0) {
			x = top[i] - 1;
			y = i;
			break;
		}
	}*/
    
	int nowtop[maxn];
	for(int i=0;i<N;++i)
		nowtop[i]=top[i];
	Tree_Node *rt=NewNode();
	++rt->n;
	int nTimes=80000,lasty=-1,times=0;
	//for(int times=1;times<=nTimes;++times)
	while(1)
	{
		int y=select(rt,M,N,nowtop,board,me);
		//_cprintf("%d ",y);
		if(rt->son[y]==0)
			rt->son[y]=NewNode();
		++rt->n,rt->w-=MonteCarlo(rt->son[y],y,M,N,nowtop,board,me,0),++times;
		double en=(double)clock()/CLOCKS_PER_SEC;
		if(en-be>2.9||nTree>7999800)
			break;
	}
	_cprintf("%d\n",times);
	y=select(rt,M,N,nowtop,board,me,false,true);
	x=top[y]-1;
	
	/*
		不要更改这段代码
	*/
	clearArray(M, N, board);
	double en=(double)clock()/CLOCKS_PER_SEC;
	_cprintf("%f\n",en-be);
	return new Point(x, y);
}


/*
	getPoint函数返回的Point指针是在本dll模块中声明的，为避免产生堆错误，应在外部调用本dll中的
	函数来释放空间，而不应该在外部直接delete
*/
extern "C" __declspec(dllexport) void clearPoint(Point* p){
	delete p;
	return;
}

/*
	清除top和board数组
*/
void clearArray(int M, int N, int** board){
	_cprintf("%d\n",nTree);
	nTree=0;
	for(int i = 0; i < M; i++){
		delete[] board[i];
	}
	delete[] board;
}


/*
	添加你自己的辅助函数，你可以声明自己的类、函数，添加新的.h .cpp文件来辅助实现你的想法
*/