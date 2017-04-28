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
#define maxn 15
#define P 131
#define mod 1000007
#define SZ(x) ((int)(x).size())
using namespace std;
typedef unsigned long long ULL;
const int me=2;
const int enemy=1;
const int WIN=2;
const int LOSE=1;
const int UNKNOWN=3;

struct msg
{
	ULL hash;
	int n,w;
	msg() {}
	msg(ULL hash,int n,int w):hash(hash),n(n),w(w) {}
};
vector<msg> score[mod+10];
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
int Find(ULL state)
{
	int x=state%mod;
	for(int i=0;i<SZ(score[x]);++i)
		if(score[x][i].hash==state)
			return i;
	return -1;
}
ULL Modify(int M,int N,ULL state,int x,int y,int **board,int v)
{
	state-=(board[x][y]+1)*Power[M*N-x*N-y-1];
	board[x][y]=v;
	state+=(board[x][y]+1)*Power[M*N-x*N-y-1];
	return state;
}
void update(ULL state,int val)
{
	int x=state%mod,i=Find(state);
	if(i>=0)
		++score[x][i].n,score[x][i].w+=val;
	else
		score[x].push_back(msg(state,1,val));
}
int randint(int l,int r)
{
	return rand()%(r-l+1)+l;
}
ULL trans(ULL nowstate,int y,int M,int N,int *top,int** board,int user_id,bool back=false)
{
	int x=top[y]-1;
	ULL ans=Modify(M,N,nowstate,x,y,board,user_id);
	--top[y];
	if(x>0&&board[x-1][y]==3)
		--top[y];
	if(back)
		top[y]=x+1,board[x][y]=0;
	return ans;
}
int select(ULL nowstate,int M,int N,int *nowtop,int** board,int cntFa,int user_id,int c=1,bool print=false)
{
	double maxv;
	int y=-1;
	for(int k=0;k<N;++k)
		if(nowtop[k]>0)
		{
			ULL state=trans(nowstate,k,M,N,nowtop,board,user_id,true);
			pair<int,int> ans=make_pair(0,0);
			int x=state%mod;
			for(int i=0;i<SZ(score[x]);++i)
				if(score[x][i].hash==state)
				{
					ans=make_pair(score[x][i].n,score[x][i].w);
					break;
				}
			if(ans.first==0)
				return k;
			double val=1.0*ans.second/ans.first;
			val+=c*sqrt(2*log(cntFa)/ans.first);
			if(y==-1||maxv<val)
				y=k,maxv=val;
			//if(print)
			//	_cprintf("(%d,%d) ",ans.first,ans.second);
		}
	//	else if(print)
	//		_cprintf("0 ");
	//if(print)
	//	_cprintf("\n");
	return y;
}

int MonteCarlo(ULL laststate,int y,int M,int N,int *top,int** board,int user_id,bool isRandom)
{
	static int can[maxn];
	int x=top[y]-1,val;
	ULL state=trans(laststate,y,M,N,top,board,user_id);
	if(user_id==me&&machineWin(x,y,M,N,board))
		val=1;
	else if(user_id==enemy&&userWin(x,y,M,N,board))
		val=1;
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
			int y,id=Find(state);
			if(id==-1)
				nextRandom=true;
			if(nextRandom)
				y=can[randint(1,n)];
			else
			{
				int cntFa=score[state%mod][id].n+1;
				y=select(state,M,N,top,board,cntFa,3-user_id);
				if(Find(trans(state,y,M,N,top,board,3-user_id,true))==-1)
					nextRandom=true;
			}
			val=-MonteCarlo(state,y,M,N,top,board,3-user_id,nextRandom);
		}
	}
	top[y]=x+1,board[x][y]=0;
	update(state,val);
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
	
	//bool used=false;
	//if(!used)
	//	AllocConsole(),used=true;
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
	if(cntChess==0)
	{
		for(int i=0;i<mod;++i)
			score[i].clear();
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
	ULL state=encode(M,N,board);
	int id=Find(state);
	if(id==-1)
	{
		update(state,0);
		id=Find(state);
	}
	msg &Fa=score[state%mod][id];
	int nTimes=100000;
	for(int times=1;times<=nTimes;++times)
	{
		int y=select(state,M,N,nowtop,board,Fa.n+1,me);
		update(state,-MonteCarlo(state,y,M,N,nowtop,board,me,0));
	}
	double maxv;
	y=select(state,M,N,nowtop,board,Fa.n,me,0,true);
	x=top[y]-1;
	
	/*
		不要更改这段代码
	*/
	clearArray(M, N, board);
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
	for(int i = 0; i < M; i++){
		delete[] board[i];
	}
	delete[] board;
}


/*
	添加你自己的辅助函数，你可以声明自己的类、函数，添加新的.h .cpp文件来辅助实现你的想法
*/