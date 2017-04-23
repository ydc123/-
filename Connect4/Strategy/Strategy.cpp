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
ULL encode(int M,int N,int **board)
{
	ULL sum=0;
	for(int i=0;i<M;++i)
		for(int j=0;j<N;++j)
			sum=sum*P+board[i][j]+1;
	return sum;
}
void update(ULL state,int val)
{
	int x=state%mod;
	for(int i=0;i<SZ(score[x]);++i)
		if(score[x][i].hash==state)
		{
			++score[x][i].n;
			score[x][i].w+=val;
			return ;
		}
	score[x].push_back(msg(state,1,val));
}
int randint(int l,int r)
{
	return rand()%(r-l+1)+l;
}
ULL trans(int y,int M,int N,int *top,int** board,int user_id,bool back=false)
{
	int x=top[y]-1;
	board[x][y]=user_id,--top[y];
	if(x>0&&board[x-1][y]==3)
		--top[y];
	ULL ans=encode(M,N,board);
	if(back)
		top[y]=x+1,board[x][y]=0;
	return ans;
}
int MonteCarlo(int y,int M,int N,int *top,int** board,int user_id)
{
	static int can[maxn];
	int x=top[y]-1,val;
	ULL state=trans(y,M,N,top,board,user_id);
	if(user_id==me&&machineWin(x,y,M,N,board))
		val=3;
	else if(user_id==enemy&&userWin(x,y,M,N,board))
		val=3;
	else
	{
		int n=0;
		for(int i=0;i<N;++i)
			if(top[i]>0)
			{
				can[++n]=i;
				int y=i,x=top[y]-1;
				board[x][y]=3-user_id;
				if(user_id==me&&userWin(x,y,M,N,board))
					n=-1;
				if(user_id==enemy&&machineWin(x,y,M,N,board))
					n=-1;
				board[x][y]=0;
				if(n<0)
				{
					val=-MonteCarlo(y,M,N,top,board,3-user_id);
					break;
				}
			}
		if(n==0)
			val=0;
		else if(n!=-1)
		{
			int y=can[randint(1,n)];
			val=-MonteCarlo(y,M,N,top,board,3-user_id);
		}
	}
	top[y]=x+1,board[x][y]=0;
	update(state,val);
	return val>0?1:-1;
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
	int x = -1, y = -1;//���ս�������ӵ�浽x,y��
	int** board = new int*[M];
	for(int i = 0; i < M; i++){
		board[i] = new int[N];
		for(int j = 0; j < N; j++){
			board[i][j] = _board[i * N + j];
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
    
	int can[maxn],n=0;
	int nowtop[maxn];
	for(int i=0;i<N;++i)
	{
		nowtop[i]=top[i];
		if(top[i]>0)
			can[++n]=i;
	}
	//_cprintf("\n");
	for(int times=1;times<=60000;++times)
	{
		int y=can[randint(1,n)];
		MonteCarlo(y,M,N,nowtop,board,me);
	}
	//_cprintf("\n");
	double maxv;
	y=-1;
	for(int k=0;k<N;++k)
		if(top[k]>0)
		{
			ULL state=trans(k,M,N,nowtop,board,me,true);
			pair<int,int> ans=make_pair(0,0);
			int x=state%mod;
			for(int i=0;i<SZ(score[x]);++i)
				if(score[x][i].hash==state)
				{
					ans=make_pair(score[x][i].n,score[x][i].w);
					break;
				}
			double val=1.0*(ans.second+1)/(ans.first+1);
			if(y==-1||maxv<val)
				y=k,maxv=val;
			_cprintf("(%d,%d) ",ans.first,ans.second);
		}
		else
			_cprintf("%.2f ",0);
	_cprintf("\n");
	x=top[y]-1;
	
	/*
		��Ҫ������δ���
	*/
	clearArray(M, N, board);
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
	for(int i = 0; i < M; i++){
		delete[] board[i];
	}
	delete[] board;
}


/*
	������Լ��ĸ�������������������Լ����ࡢ����������µ�.h .cpp�ļ�������ʵ������뷨
*/