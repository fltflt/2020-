# 2020-Huawei-CodeCraft
2020华为软件精英挑战赛成渝赛区初赛第9，复赛第3，决赛全国第9解决方案

# 成绩
队伍：少年队

初赛：成渝赛区Rank 9/1034

复赛：成渝赛区Rank 3

决赛：全国总榜Rank 9

# 比赛题目与背景
通过给定的资金流水，检测并输出指定约束条件的所有循环转账；
初赛为有向图中找出所有长度为3到7的环；
决赛为计算每个有向图每个节点的位置关键中心性并输出top100。

# 初赛分析

## (1) 基本解题流程：

> 读图预处理(去除特殊节点)->储存图(前向星)->dfs找环(正向3+反向4)->输出结果

## (2) 基本解题思路：

> 采用“3+4”模式：反向图BFS搜3层，存储合法的搜索路径以及长度为3的环路；正向图DFS搜4层，搜索中利用反向图已有结果直接拼接，即可得到长度为4-7的环路

## (3) 优化trick：
1.使用局部变量，减少使用全局变量;

2.使用数组代替vector;

3.保持结构体字节对齐;

4.将id和边尽可能的连续，提高cache的命中率;

5.更改数据类型，减少计算时间;

6. 针对数据特点优化：
转账金额较小的这一点，可以使用动态的数据类型，如自动切换的uint_64,uint_32,uint_16（提升100+）
第一组：菊花图（无标度网络），存在大量入度为0，出度为1的结点
第二组：随机图，90%以上的点只有一个前驱，边权为100以内的正态分布，均匀度为20左右，且分布均匀，因此搜索四次邻接表即可完成全图搜索对任意一点，所有点均会入堆至少一次
第三组：第一组+第二组综合

# 决赛分析

## (1) 基本解题流程：

> 读图预处理->储存图->dijkstra计算最短路+优先队列->计算位置关键中心性->输出结果

## (2) 基本解题思想：

> 以每个点出发做dijstra，求出到个点的单源最短路径，并且按拓扑序反向递推计算中心性bc(算法参考Brandes U. A faster algorithm for betweenness centrality[J]. Journal of mathematical sociology, 2001, 25(2): 163-177.)

## (3) 优化trick：

1.使用局部变量，减少使用全局变量;

2.使用数组代替vector;

3.保持结构体的定义 保持字节对齐;

4.将id和边尽可能的连续，提高cache的命中率;

5.更改数据类型，减少计算时间;

