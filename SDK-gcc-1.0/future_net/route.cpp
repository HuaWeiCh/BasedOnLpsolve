#include <time.h> 
#include <stdio.h>
#include "route.h"
#include "lib_io.h"
#include "lp_lib.h"
#include "lib_record.h"

#define debug 0

int	 pNum;
int  endP;
int  startP;
int  lNum;
int	 repeatLineNum=0;
int	 line_id[4801];
int	 line_end[4801];
int	 line_start[4801];
int	 line_length[4801];
int	 common_start_index[1201];
int  common_start_num[1201]={0};//考虑到点的编号不连续,1201应该足够了吧
int  mustNum;
int  mustP[51];
int  pathNum=0;
int  path[4801];
int	 path_end[4801];			//用来记录对应path[i]的line_end
int	 nowLength;					//用于dfs搜索结果时,记录每一步权值
int  pathLength;
int  successPath[4801];
bool *ifmustP;
bool *ifVisited;
bool success=false;
REAL *row;

clock_t t1, t2;


extern int len;					//如果需要多次写入结果,写入前须清零
extern char *Result_file;		//指向result.scv
//*****************************************CatchData函数***************************************//
void catch_data(char *graph[5000], int edge_num, char *condition)
{
//***************************读取有向图**************************************
	int	count=1;
	int	l_id[1201][8];
	int	l_end[1201][8];
	int	l_start[1201][8];
	int	l_length[1201][8];
	int id,start,end,length;

	for(int i=0;i<edge_num;i++)
	{
		sscanf(graph[i],"%d,%d,%d,%d",&id,&start,&end,&length);
		for(int j=0;j<common_start_num[start];j++)//去重复，并保留权值最小
		{
			if(l_end[start][j]==end)
			{
				repeatLineNum++;
				if(length<l_length[start][j])
				{
					l_id[start][j]	 =id;
					l_length[start][j]=length;
				}
				goto repeat;
			}
		}
		l_id[start][common_start_num[start]]	=id;
		l_start[start][common_start_num[start]]	=start;
		l_end[start][common_start_num[start]]	=end;
		l_length[start][common_start_num[start]]=length;
		common_start_num[start]++;
		if(pNum<start)				//寻点数
            pNum=start;
        if(pNum<end)
            pNum=start;
        repeat:	;
	}
	lNum=edge_num-repeatLineNum;	//记录 有向线 数目
	
	for(int i=0;i<pNum+1;i++)			//转换为一维矩阵
	{
		common_start_index[i]=count;
		for(int j=0;j<common_start_num[i];j++)
		{
			line_id[count]		=l_id[i][j];
			line_end[count]		=l_end[i][j];
			line_start[count]	=l_start[i][j];
			line_length[count]	=l_length[i][j];
			count++;
		}
	}

#if debug
for(int i=1;i<lNum+1;i++)
	printf("The line is:%4d %4d %4d %4d\n",line_id[i],line_start[i],line_end[i],line_length[i]);
for(int i=0;i<pNum+1;i++)	printf("The common_start_num is:%d\n",common_start_num[i]);	
#endif
//**********************************读取必过点****************************************
    ifmustP=new bool[pNum+1]; 		//根据顶点数初始化标志长度
    for(int i=0;i<=pNum;i++)		//初始化顶点标记
    {
        ifmustP[i]=false;
    }

	int temp0=0;					//起始点
	int temp1=0;
	temp0=*condition;
	while((temp0>=48)&&(temp0<=57))
	{
		temp1=temp1*10+temp0-48;
		condition++;
		temp0=*condition;
	}
	startP=temp1;
//*************************************
	temp1=0;						//终止点
	condition++;
	temp0=*condition;
	while((temp0>=48)&&(temp0<=57))
	{
		temp1=temp1*10+temp0-48;
		condition++;
		temp0=*condition;
	}
	endP=temp1;
//*************************************
	condition++;					//必过点
	mustNum=0;
	temp0=*condition;
	while(10!=temp0)
	{
		while((temp0>=48)&&(temp0<=57))
		{
			mustP[mustNum]=mustP[mustNum]*10+temp0-48;
			condition++;
			temp0=*condition;
			if((124!=temp0)&&((temp0<48)||(temp0>57)))	goto theEnd;
		}
		condition++;
		temp0=*condition;
		//ifmustP[mustP[mustNum]]=true;
		mustNum++;
	}
	theEnd:
		mustNum++;
	for(int i=0;i<mustNum;i++)	ifmustP[mustP[i]]=true;//初始化必过标志

#if debug
	printf("\n");
	printf("The mustNum is:%d\n",mustNum);
	for(int i=0;i<mustNum;i++)	printf("The mustP is:%d\n",mustP[i]);

	printf("\n");
    printf("The pNum is %d\n",pNum);
    printf("The lNum is %d\n",lNum);
    printf("The repeatLineNum is %d\n",repeatLineNum);
    printf("\n");
    printf("The startP is %d\n",startP);
    printf("The endP is %d\n",endP);
#endif
}
//*********************************set_outdegree_constraint函数********************************//
void set_outdegree_constraint(lprec *lp,int start,int constr_type,REAL rh)
{
	REAL *row=new REAL[common_start_num[start]];
	int	 *colon=new int[common_start_num[start]];

	for(int i=0;i<common_start_num[start];i++)
	{
		row[i]=1;
		colon[i]=common_start_index[start]+i;
	}
	add_constraintex(lp,common_start_num[start],row,colon,constr_type,rh);
	delete[] row;
	row=NULL;
	delete[] colon;
	colon=NULL;
}
//**********************************set_indegree_constraint函数********************************//
void set_indegree_constraint(lprec *lp,int end,int constr_type,REAL rh)
{
	row[0]=0;
	for(int i=1;i<lNum+1;i++)
	{
		if(line_end[i]==end)
		{
			row[i]=1;
		}
		else
		{
			row[i]=0;
		}
	}

	add_constraint(lp,row,constr_type,rh);
}
//****************************************get_result函数***************************************//
int get_result(lprec *lp)
{
	int	row_num;
	int colum_num;
	int	length;
	int index=0;

	colum_num=get_Ncolumns(lp);
	row_num=get_Nrows(lp);

	REAL *result=new REAL[1+row_num+colum_num];

 	get_primal_solution(lp,result);

 	for(int i=0;i<=lNum+1;i++)	ifVisited[i]=false;

	for(int i=row_num+1;i<1+row_num+colum_num;i++)
	{
		index++;
		if(0!=result[i])
		{
			//printf("The path is:%d\n",index);
			ifVisited[index]=true;
		}
	}
	length=result[0];
	delete[] result;
	result=NULL;
	return length;

/*	int	length;
	int rowNum;
	int result[lNum];
	
	rowNum=get_Norig_rows(lp);//get_Nrows
	for(int i=1;i<lNum+1;i++)
	{
		result[i]=get_var_primalresult(lp,rowNum+i);
		if(result[i])
		{
			//printf("The path is:%d\n",i);
			ifVisited[i]=true;
		}
		else			ifVisited[i]=false;
	}
	length=get_var_primalresult(lp,0);
	//printf("The length is:%d\n",length);
	return length;
*/
}
//********************************************dfs函数******************************************//
void dfs(lprec *lp,int cur)
{
	REAL differenceValue;

	for(int i=0;i<common_start_num[path_end[cur-1]];i++)
	{
		if(true==ifVisited[common_start_index[path_end[cur-1]]+i])
		{
			path[cur]	 =line_id[common_start_index[path_end[cur-1]]+i];
			path_end[cur]=line_end[common_start_index[path_end[cur-1]]+i];
			nowLength	+=line_length[common_start_index[path_end[cur-1]]+i];
			ifVisited[common_start_index[path_end[cur-1]]+i]=false;
			if(path_end[cur]==endP)
			{
				if(nowLength==pathLength)
				{
                    len=0;
                    pathNum=cur;
                    for(int j=1;j<=cur;j++)
                    {
#if debug
                        successPath[j]=path[j];
#endif
                        record_result(path[j]);
                    }
                    write_result(Result_file);
                	success=true;
                	return;
				}
				else
				{
					row[0]=0;
					for(int j=1;j<lNum+1;j++)
					{
						if(true==ifVisited[j])	row[j]=line_length[j];
						else					row[j]=0;
					}
					differenceValue=pathLength-nowLength-1;
					add_constraint(lp,row,LE,differenceValue);
					return;
				}
			}
			dfs(lp,cur+1);
			ifVisited[common_start_index[path_end[cur-1]]+i]=true;
			nowLength -= line_length[common_start_index[path_end[cur-1]]+i];
		}
	}
}
//***************************************search_route函数**************************************//
//你要完成的功能总入口---相比于你的main函数
void search_route(char *Graph[5000], int Edge_num, char *Condition)
{
	int ret=0;										//记录solve函数的返回值
	t1=clock();
	catch_data(Graph,Edge_num,Condition);			//读取文件中数据并按规律存储

    //初始化数据
    ifVisited=new bool[lNum+1]; 					//根据有向线数初始化标志长度
    path_end[0]=startP;								//初始化path路径索引
    row=new REAL[lNum+1];
//***************************************模型建立及求解*****************************************
	lprec *lp;

	lp = make_lp(0,lNum);							//创建一个新的LP模型
	if(lp == NULL)
	{
		fprintf(stderr, "Unable to create new LP model!\n");
		return;
	}
//********************************加约束*********************************
	set_add_rowmode(lp, TRUE);						//first! set the objective function
	/* now add the constraints */
//*********************设置变量类型binary*********************
	for(int i=1;i<lNum+1;i++)	set_binary(lp,i,true);
//********************添加出度和入度的约束********************
	for(int i=0;i<=pNum;i++)
	{
		if(common_start_num[i]>0)
		{
			if(i==startP)		//巧妙地避过start和must重复
			{
				set_indegree_constraint(lp,i,EQ,0);
				set_outdegree_constraint(lp,i,EQ,1);
			}
			else if(i==endP)	//巧妙地避过end和must重复
			{
				set_indegree_constraint(lp,i,EQ,1);
				set_outdegree_constraint(lp,i,EQ,0);
			}
			else if(true==ifmustP[i])
			{
				set_indegree_constraint(lp,i,EQ,1);
				set_outdegree_constraint(lp,i,EQ,1);
			}
			else//此处可能会多加不必要的约束条件(点可以不连续),不知会不会影响解得最优
			{
				set_indegree_constraint(lp,i,GE,0);
				set_indegree_constraint(lp,i,LE,1);
				set_outdegree_constraint(lp,i,GE,0);
				set_outdegree_constraint(lp,i,LE,1);
//*********普通点出度等于入度***********
				row[0]=0;
				for(int j=1;j<lNum+1;j++) 
				{
					if(line_end[j]==i)	{row[j]=1;}
					else				{row[j]=0;}
				}
	
				for(int j=0;j<common_start_num[i];j++)
				{
					row[common_start_index[i]+j]=row[common_start_index[i]+j]-1;
				}
				
				add_constraint(lp,row,EQ,0);
//**************************************
			}
		}
	}

//*************************设置minmize************************
	for(int i=1;i<lNum+1;i++)
	{
		row[i]=line_length[i];
	}

	set_obj_fn(lp,row);
	//set_timeout(lp,2);
	//set_break_at_first(lp,TRUE);
//**********************设置presolve预处理********************
	//set_presolve(lp,PRESOLVE_ROWS|PRESOLVE_LINDEP,get_presolveloops(lp));
	//set_presolve(lp,PRESOLVE_ROWS,get_presolveloops(lp));
	
	/* end of adding constraints */
	set_add_rowmode(lp, FALSE);
//**********调用solve函数求解,若有环,加约束,继续求解**********
	//t1=clock();
	while(1>=ret)
	{
		t2=clock();
		if(((t2-t1)/1000)>50)
		{
			set_verbose(lp,0);
			set_timeout(lp,2);
			set_break_at_first(lp,TRUE);
		}
		ret = solve(lp);
#if debug
		printf("The ret is:%d\n",ret);
#endif
		pathLength=get_result(lp);
		dfs(lp,1);
		if(true==success)	break;
		nowLength=0;
	}
//***************************打印模型*************************
	//print_lp(lp);
//***********************************************************************
	delete_lp(lp);									//求解结束,删除LP模型
//**********************************************************************************************	
#if debug
    if(true==success)							//调试时的结果输出
	{
	    printf("pathLength is %d\n",pathLength);//打印权值
	    printf("Path is :");					//打印最后路径
	    for(int i=1;i<=pathNum;i++)
	    	printf("%4d",successPath[i]);
	    printf("\n");
	}
	else
	{
		printf("Path is : NA!\n");
	}
#endif
}
//*********************************************The end!****************************************//

