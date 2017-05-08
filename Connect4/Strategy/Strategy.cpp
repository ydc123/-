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
	���Ժ����ӿ�,�ú������Կ�ƽ̨����,ÿ�δ��뵱ǰ״̬,Ҫ�����������ӵ�,�����ӵ������һ��������Ϸ��������ӵ�,��Ȼ�Կ�ƽ̨��ֱ����Ϊ��ĳ�������
	
	input:
		Ϊ�˷�ֹ�ԶԿ�ƽ̨ά����������ɸ��ģ����д���Ĳ�����Ϊconst����
		M, N : ���̴�С M - ���� N - ���� ����0��ʼ�ƣ� ���Ͻ�Ϊ����ԭ�㣬����x��ǣ�����y���
		top : ��ǰ����ÿһ���ж���ʵ��λ��. e.g. ��i��Ϊ��,��_top[i] == M, ��i������,��_top[i] == 0
		_board : ���̵�һά�����ʾ, Ϊ�˷���ʹ�ã��ڸú����տ�ʼ���������Ѿ�����ת��Ϊ�˶�ά����board
				��ֻ��ֱ��ʹ��board���ɣ����Ͻ�Ϊ����ԭ�㣬�����[0][0]��ʼ��(����[1][1])
				board[x][y]��ʾ��x�С���y�еĵ�(��0��ʼ��)
				board[x][y] == 0/1/2 �ֱ��Ӧ(x,y)�� ������/���û�����/�г������,�������ӵ㴦��ֵҲΪ0
		lastX, lastY : �Է���һ�����ӵ�λ��, ����ܲ���Ҫ�ò�����Ҳ������Ҫ�Ĳ������ǶԷ�һ����
				����λ�ã���ʱ��������Լ��ĳ����м�¼�Է������ಽ������λ�ã�����ȫȡ�������Լ��Ĳ���
		noX, noY : �����ϵĲ������ӵ�(ע:��ʵ���������top�Ѿ����㴦���˲������ӵ㣬Ҳ����˵���ĳһ��
				������ӵ�����ǡ�ǲ������ӵ㣬��ôUI�����еĴ�����Ѿ������е�topֵ�ֽ�����һ�μ�һ������
				��������Ĵ�����Ҳ���Ը�����ʹ��noX��noY��������������ȫ��Ϊtop������ǵ�ǰÿ�еĶ�������,
				��Ȼ�������ʹ��lastX,lastY�������п��ܾ�Ҫͬʱ����noX��noY��)
		���ϲ���ʵ���ϰ����˵�ǰ״̬(M N _top _board)�Լ���ʷ��Ϣ(lastX lastY),��Ҫ���ľ�������Щ��Ϣ�¸������������ǵ����ӵ�
	output:
		������ӵ�Point
*/
extern "C" __declspec(dllexport) Point* getPoint(const int M, const int N, const int* top, const int* _board, 
	const int lastX, const int lastY, const int noX, const int noY){
	/*
		��Ҫ������δ���
	*/
	bool used=false;
	if(!used)
		AllocConsole(),used=true;
	double be=(double)clock()/CLOCKS_PER_SEC;
	int cntChess=0;
	int x = -1, y = -1;//���ս�������ӵ�浽x,y��
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
		�������Լ��Ĳ������������ӵ�,Ҳ���Ǹ�����Ĳ�����ɶ�x,y�ĸ�ֵ
		�ò��ֶԲ���ʹ��û�����ƣ�Ϊ�˷���ʵ�֣�����Զ����Լ��µ��ࡢ.h�ļ���.cpp�ļ�
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
		��Ҫ������δ���
	*/
	clearArray(M, N, board);
	double en=(double)clock()/CLOCKS_PER_SEC;
	_cprintf("%f\n",en-be);
	return new Point(x, y);
}


/*
	getPoint�������ص�Pointָ�����ڱ�dllģ���������ģ�Ϊ��������Ѵ���Ӧ���ⲿ���ñ�dll�е�
	�������ͷſռ䣬����Ӧ�����ⲿֱ��delete
*/
extern "C" __declspec(dllexport) void clearPoint(Point* p){
	delete p;
	return;
}

/*
	���top��board����
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
	������Լ��ĸ�������������������Լ����ࡢ����������µ�.h .cpp�ļ�������ʵ������뷨
*/