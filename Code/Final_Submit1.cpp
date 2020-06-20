#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <utility>
#include <vector>
#include <iostream>
#include <algorithm>
#include <fstream>
#include <cmath>
#include <mutex>
#include <cstdlib>
#include <numeric>
#include <time.h>
#include <string.h>
#include <stdarg.h>
#include <map>
#include <iomanip>
#include <fstream>
#include <sys/stat.h>
#include <stdlib.h>
#include <sys/types.h>
#include <fcntl.h>
#include <queue>
#include <stack>
#include <exception>
#include <set>
#include<atomic> 

//#define IS_DEBUG_MODE                       // debug 模式
#define LINUX_SYSTEM						// LINUX or WINDOWS 操作系统

#ifdef LINUX_SYSTEM
#include <sys/ioctl.h>
#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <unistd.h> 
#else
#include <Windows.h>
#endif

#define unlikely(x) __builtin_expect(!!(x), 0)
#define likely(x) __builtin_expect(!!(x), 1) 

#define NUM_THREADS 12	                    // 线程个数  
#define ALL_NUM_THREADS 12
#define STD_NUM_THREADS 8					// 标准线程个数
#define MAX_RECORDS 2500001                 // 最多转账记录数
#define MAX_NODES 1000001					// 最多转账记录数
#define MAX_SUB_RECORDS 1000000             // 子线程内部最多的转账记录数
#define LLONG_MAX 922337203685477580		// long long 最大值
#define MAX_NODES_IN_MIN_PATHS	MAX_NODES	// 从s开始能走到的节点的个数的最大值，它不会大于节点数
#define KEY_THRESHOLD 6000

#define SIZE_GROUP 8						// 分组的大小

#define SIZE_OF_UI(n) (n << 2)
#define TOP_N       100

#define NPRINT_PER_NG 20					// 每隔多久打印一次

typedef unsigned long long uint64;
typedef unsigned int uint32;

struct _edge_org {
	uint32 from;
	uint32 to;
	uint32 money;
};

/**
 * 长度为32的边
 */
struct _edge_T {
	//ui from;
	uint32 to;
	uint32 money;
};


// 正向比较函数
auto cmp_forward = [](const _edge_org& item1, const _edge_org& item2) {
	if (item1.from < item2.from) {
		return true;
	}
	else if (item1.from > item2.from) {
		return false;
	}
	else {
		return item1.to < item2.to;
	}
};


typedef struct {
	int out_degree = 0;
	int in_degree = 0;
} _degree;

typedef struct
{
	uint32 node = 0;
	double value;
} _centraility;

// global variables
static int n_nodes;							// 节点个数
static int n_records;						// 转账记录条数
static int n_group;							// 分组个数

static _edge_org forwardG_org[MAX_RECORDS];
static _edge_T total_forwardG[MAX_RECORDS];         // 图，用一维前向星结构存储
static int total_head_next[MAX_NODES];		// 图相关，记录每一个节点的邻接点在图中的位置
static _degree degrees[MAX_NODES];				// 出入度信息
static _centraility centrality[MAX_NODES];		// 节点关键信息
static int total_special_node_flag[MAX_NODES];		// 记录特殊节点的相关信息
//static std::atomic<int> i_group;				// 原子变量，用于判断并行处理到哪一个组了
static std::vector<uint32> map_to_org;				// 存储每一个节点的原始节点id值
static std::vector<uint32> new_map_to_org;			// 存储每一个节点的原始节点id值

static int data_type_flag = 64;

typedef struct
{
	int start = 0;	// 组内第一个点的id
	int end = 0;	// 组内最后一个点的id
} _group_info;

// 线程分组处理
std::vector<_group_info> groups;

/**
 * 工具函数
 */
template <class T>
inline void gCopy(T*& dst, const T* src, const int n) {
	dst = new T[n];
	memcpy(dst, src, sizeof(T) * n);
}

template <class T>
inline void gAlloc(T*& dst, const int n, const bool is_init_zero = false) {
	dst = new T[n];
	if (is_init_zero) {
		memset(dst, 0, sizeof(T) * n);
	}
}

// 判断一个char是否为数字
inline bool is_digit(char ch) {
	return (ch >= '0' && ch <= '9');
}

// 根据任务数量和线程数对一个目标任务进行分块
template <class T>
void split_to_blocks(const int& n, int m_threads, T* v) {


	uint32 interval = uint32(n / m_threads);
	v[0].start = 0;

	for (int i = 0; i < m_threads - 1; ++i) {
		v[i].end = interval + v[i].start;
		v[i + 1].start = v[i].end;
	}
	v[m_threads - 1].end = n;
}

// 计时器
#ifdef IS_DEBUG_MODE

#ifndef LINUX_SYSTEM
int gettimeofday(struct timeval* tp, void* tzp)
{
	time_t clock;
	struct tm tm;
	SYSTEMTIME wtm;
	GetLocalTime(&wtm);
	tm.tm_year = wtm.wYear - 1900;
	tm.tm_mon = wtm.wMonth - 1;
	tm.tm_mday = wtm.wDay;
	tm.tm_hour = wtm.wHour;
	tm.tm_min = wtm.wMinute;
	tm.tm_sec = wtm.wSecond;
	tm.tm_isdst = -1;
	clock = mktime(&tm);
	tp->tv_sec = clock;
	tp->tv_usec = wtm.wMilliseconds * 1000;
	return (0);
}
#endif

struct Timer
{
	double total = 0;
	timeval tic, toc;

	Timer()
	{
		gettimeofday(&tic, NULL);
	}

	void stop(const char* name)
	{
		gettimeofday(&toc, NULL);
		printf("|%s: %.3fs \n", name, double(toc.tv_sec - tic.tv_sec) + double(toc.tv_usec - tic.tv_usec) / 1000000);
	}

	void reset() {
		gettimeofday(&tic, NULL);
	}

	void add() {
		gettimeofday(&toc, NULL);
		total += double(toc.tv_sec - tic.tv_sec) + double(toc.tv_usec - tic.tv_usec) / 1000000;
	}

	void print(const char* name) {
		gettimeofday(&toc, NULL);
		printf("|%s: %.3fs \n", name, total);
	}
};
#endif

template <class T>
struct _Block
{
	T start;
	T end;
};

/**
 * 输入数据分块，为了方便读取
 */
struct _InputDataBlock {
	uint32 start;
	uint32 end;
	int n_edge = 0;
	_edge_org* edges = NULL;

	_InputDataBlock() {
		edges = NULL;
		n_edge = 0;
	}

	void clear() {
		if (edges) {
			delete[] edges;
			edges = NULL;
		}
	}

	void set_edge_size(uint32 size = MAX_SUB_RECORDS) {
		gAlloc(edges, size);
	}

	~_InputDataBlock() {
		clear();
	}
};

/**
 * 存图用的类
 */
struct Graph {
	// 用于将原始id值全部映射到新的id值
	std::unordered_map<uint32, uint32> map_to_new;
	// 存储读取到的每一个数据
	_InputDataBlock input_blocks[STD_NUM_THREADS];

	// 将每一个块的数据的起始位置指向一个digit，终止字符指向'\n'
	void modify_end_ptr_to_new_line(char*& buf, _InputDataBlock* pBlock) {
		for (int i = 0; i < STD_NUM_THREADS - 1; i++) {
			auto& block = pBlock[i];
			while (buf[block.end] != '\n') {
				block.end++;
			}
			pBlock[i + 1].start = block.end + 1;
		}

		auto& block = pBlock[STD_NUM_THREADS - 1];

		while (!is_digit(buf[block.end])) {
			block.end--;
		}
		block.end++;
	}


	// 读取一个块的数据
	void read_one_block(char*& p, _InputDataBlock& block) {

		uint32 s, t;
		uint64 m;
		char ch;

		uint32 i = block.start;
		const uint32 end = block.end;
		_edge_org*& edges = block.edges;
		int& n_edge = block.n_edge;

		// 初始化边的数量为0
		n_edge = 0;

		// 定位到第一个数字
		while (!is_digit(p[i]))     i++;

		while (i < end) {
			s = t = 0;
			m = 0;

			while ((ch = p[i++]) != ',')    s = (s * 10 + ch - '0');
			while ((ch = p[i++]) != ',')    t = (t * 10 + ch - '0');

			while (is_digit(p[i]))           m = (m * 10 + p[i++] - '0');

			while (i < end && !is_digit(p[i]))         i++;

			if (m != 0) {
				edges[n_edge].from = s;
				edges[n_edge].to = t;
				edges[n_edge++].money = m;
			}

		}
	}

	/**
	 * 合并读取到的所有数据并排序计算节点的数量
	 * Input:
	 * block: 输入数据块（一个线程处理一块）
	 * nodes: 存储所有的节点id值
	 */
	void merge_and_sort(_InputDataBlock* block, std::vector<uint32>& nodes) {


		nodes.reserve(MAX_RECORDS << 1);
		nodes.clear();

		int i_edge = 0, i_node = 0;
		n_records = 0;

		// 将所有的边融合到一起
		for (int i = 0; i < STD_NUM_THREADS; i++) {
			n_records += block[i].n_edge;

			for (int j = 0; j < block[i].n_edge; j++) {
				// 赋值第i个数据块中第j条边
				auto& jedge = block[i].edges[j];
				forwardG_org[i_edge++] = jedge;

				// 添加from和to到节点列表
				nodes.emplace_back(jedge.from);
				nodes.emplace_back(jedge.to);
			}
		}

		// 对所有的边和节点排序（每一个任务开启一个线程去处理）

		std::thread t1 = std::thread([]() {
			std::sort(forwardG_org, forwardG_org + n_records, cmp_forward);
			});

		// 排序节点
		std::thread t2 = std::thread([&nodes, &i_node]() {
			std::sort(nodes.begin(), nodes.end());
			});

		t1.join();
		t2.join();

		// 删除掉重复的节点
		nodes.erase(std::unique(nodes.begin(), nodes.end()), nodes.end());

		// 设置节点个数
		n_nodes = nodes.size();
	}

	// 映射节点
	void map_part_ids_by_map(const int pid) {

		for (int k = pid; k < n_records; k += STD_NUM_THREADS) {
			auto& from = forwardG_org[k].from;
			auto& to = forwardG_org[k].to;

			from = map_to_new[from];
			to = map_to_new[to];
		}
	}

	// 映射节点
	void map_part_ids_by_vector(const int pid, const uint32* vec_map_to_new) {

		for (int k = pid; k < n_records; k += STD_NUM_THREADS) {
			auto& from = forwardG_org[k].from;
			auto& to = forwardG_org[k].to;

			from = vec_map_to_new[from];
			to = vec_map_to_new[to];
		}
	}

	// 将原始节点id映射到新的有序节点id
	void create_map_by_map(uint32* map_to_org) {

		//map_to_new.clear();

		map_to_new.reserve(n_nodes);

		for (int k = 0; k < n_nodes; k++) {
			map_to_new[map_to_org[k]] = k;
		}
	}

	// 将图里面所有的边的id全部映射为新的id
	void map_ids(uint32* map_to_org) {

		create_map_by_map(map_to_org);

		std::thread ts[STD_NUM_THREADS];
		for (int i = 0; i < STD_NUM_THREADS; i++) {
			ts[i] = std::thread(&Graph::map_part_ids_by_map, this, i);
			//map_part_ids(i);
		}

		for (int i = 0; i < STD_NUM_THREADS; ++i)   ts[i].join();
	}

	void bfs_reset_id(const int st, int& k, bool* visit) {

		if (visit[st]) {
			return;
		}

		visit[st] = true;
		std::queue<uint32> qu;
		qu.push(st);
		uint32 org_id;
		//new_map_to_org.resize(n_nodes);
		while (!qu.empty()) {
			uint32 now = qu.front();
			//org_id = map_to_org[now];
			qu.pop();

			new_map_to_org[k++] = now;


			for (int i = total_head_next[now], j = total_head_next[now + 1]; i < j; i++) {
				auto& to = forwardG_org[i].to;
				if (!visit[to]) {
					visit[to] = true;
					qu.push(to);
				}
			}
		}


	}

	void bfs_all() {
		bool* visit;
		gAlloc(visit, n_nodes, true);
		new_map_to_org.resize(n_nodes);


		int k = 0;
		for (int i = 0; i < n_nodes; i++) {
			bfs_reset_id(i, k, visit);
		}

		delete[] visit;

		// 利用bfs序做第二次映射
		//map_ids(new_map_to_org.data());
		std::vector<uint32> vec_map_to_new(n_nodes);
		for (int k = 0; k < n_nodes; k++) {
			vec_map_to_new[new_map_to_org[k]] = k;
		}

		std::thread ts[STD_NUM_THREADS];
		for (int i = 0; i < STD_NUM_THREADS; i++) {
			ts[i] = std::thread(&Graph::map_part_ids_by_vector, this, i, vec_map_to_new.data());
		}

		for (int i = 0; i < STD_NUM_THREADS; ++i)   ts[i].join();

		// sort edge
		std::sort(forwardG_org, forwardG_org + n_records, cmp_forward);

	}

	// 计算每一个节点在图中存放的位置，并统计节点的出入度
	void set_head_info() {

		// 初始化出入度
		memset(degrees, 0, sizeof(_degree) * n_nodes);

		// 设置flag位
		uint64 max_edge = 0;

		for (int i = 0; i < n_records; ++i) {
			auto& item = forwardG_org[i];
			degrees[item.from].out_degree++;
			degrees[item.to].in_degree++;

			max_edge = max_edge > forwardG_org[i].money ? max_edge : forwardG_org[i].money;
		}

		int offset = 0;
		for (int i = 0; i < n_nodes; ++i) {
			//head_next[i] = { offset, offset + degrees[i].out_degree };
			total_head_next[i] = offset;
			offset += degrees[i].out_degree;
		}
		total_head_next[n_nodes] = offset;

		new_map_to_org = map_to_org;
		//// 开始重新映射id
		bfs_all();

		// 重新构图
		memset(degrees, 0, sizeof(_degree) * n_nodes);
		for (int i = 0; i < n_records; ++i) {
			auto& item = forwardG_org[i];
			degrees[item.from].out_degree++;
			degrees[item.to].in_degree++;
		}

		offset = 0;
		for (int i = 0; i < n_nodes; ++i) {
			total_head_next[i] = offset;//{ offset, offset + degrees[i].out_degree };
			offset += degrees[i].out_degree;
		}
		total_head_next[n_nodes] = offset;

		// 拷贝图
		if (max_edge < 2000) {
			data_type_flag = 32;
		}
		else {
			data_type_flag = 64;
		}

		for (int i = 0; i < n_records; i++) {
			total_forwardG[i].to = forwardG_org[i].to;
			total_forwardG[i].money = forwardG_org[i].money;
		}
	}

	// 统计有哪些特殊节点（入度为0，初度为1）：这样的点后面不需要去计算centrality
	void statistical_special_nodes() {
		// 初始化特殊节点信息
		memset(total_special_node_flag, 0, sizeof(int) * n_nodes);

		for (int i = 0; i < n_nodes; i++) {
			if (degrees[i].in_degree == 0 && degrees[i].out_degree == 1) {
				auto& edge = forwardG_org[total_head_next[i]];
				// flag 值为1表示该节点出度为1，入度为0
				total_special_node_flag[edge.from] = 1;

				// flag 值为2表示特殊节点的邻接节点
				if (total_special_node_flag[edge.to] == 0) {
					total_special_node_flag[edge.to] = 2;
				}
				else {
					total_special_node_flag[edge.to]++;
				}
			}
			else if (degrees[i].out_degree == 0) {
				//auto& edge = forwardG_org[head_next[i]];
				total_special_node_flag[i] = 1;
			}
		}
	}

	// 读取数据，主要的函数
	void load_data(const std::string& test_data_file) {
#ifdef IS_DEBUG_MODE
		Timer t0;
#endif

#ifdef LINUX_SYSTEM
		struct stat sb;
		int fd = open(test_data_file.c_str(), O_RDONLY);
		fstat(fd, &sb);
		int size = sb.st_size;
		char* buf = (char*)mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);

		if (fd < 0) {
			std::cout << "打开训练文件失败\n" << test_data_file << std::endl;
			exit(0);
			return;
		}

#else
		std::ifstream t(test_data_file);
		t.seekg(0, std::ios::end);
		size_t size = t.tellg();
		char* buf = new char[size + 100];
		t.seekg(0);
		t.read(buf, size);

#endif


		// 设置每个数据块的大小
		_InputDataBlock input_data_block[STD_NUM_THREADS];
		for (int i = 0; i < STD_NUM_THREADS; i++) input_data_block[i].set_edge_size(MAX_RECORDS);
		split_to_blocks(size - 1, STD_NUM_THREADS, input_data_block);

		// 轻微地偏移每个数据块的起始和终止位置，保证起始位置指向行头，终止位置指向行尾
		modify_end_ptr_to_new_line(buf, input_data_block);

		// 启动多线程读取数据
		std::thread ts[STD_NUM_THREADS];
		for (int i = 0; i < STD_NUM_THREADS; i++) {
			ts[i] = std::thread(&Graph::read_one_block, this, std::ref(buf), std::ref(input_data_block[i]));
			n_records += input_data_block[i].n_edge;
		}

		for (int i = 0; i < STD_NUM_THREADS; ++i)   ts[i].join();

		// 合并读取到的数据并排序和统计所有的节点
		merge_and_sort(input_data_block, map_to_org);

		// 映射节点
		map_ids(map_to_org.data());

		// 构图
		set_head_info();

		// 统计特殊节点数量
		statistical_special_nodes();

#ifdef LINUX_SYSTEM
		// 销毁内存
		close(fd);
		munmap(buf, sb.st_size);
#else
		t.close();
		delete[] buf;
#endif

#ifdef IS_DEBUG_MODE
		t0.stop("Prepare");
		printf("#n_records:%d, n_nodes:%d", n_records, n_nodes);
#endif
	}
};


// 存储每个节点当前对应的最短路径，方便优先对立pop出当前最段路径所对应的节点
template <class T>
struct _node_weight {
	uint32 first;
	T second;
};

// 比较两个节点，哪一个是从s所到的最短路径，优先队列需要
template <class T>
struct cmp_weight {
	bool operator() (const _node_weight<T>& a, const _node_weight<T>& b) {//默认是less函数
		//return a.weight > b.weight;
		return a.second > b.second;
	}
};

/**
 * 存储每个节点在寻找最短路径的过程中所产生的一系列信息
 */
struct Dis {
	//bool visit;					// 是否被访问
	uint32 sigma;						// sigma值
	uint32 n_used;						// 前置节点个数
	uint32 pre_start;					// 前置节点在一维数组中的位置

	Dis() {
	}

	// 在计算新的s到其它所有节点的最短路径是，需要调用该函数
	inline void reset() {
		//weight = -1;
		sigma = 0;
		n_used = 0;
		//visit = false;
	}
};


template <class T1, class T2>
struct VMap {
	// 采用两种映射方式，当key值小于一个数的时候我们用map映射，当key值大于一个
	std::unordered_map<T2, std::vector<uint32>> map_dist;
	std::priority_queue<T2, std::vector<T2>, std::greater<T2>> Q_set;
	std::vector<uint32> v_dist[KEY_THRESHOLD];

	T2 min_offset;

	inline void set_min_offset(const T2& offset) {
		min_offset = offset;
	}

	/*
	* =====================================================================================
	* DIJ 的算法，插入新的节点到优先队列中的操作
	* =====================================================================================
	*/
	inline void insert(const uint32 id, const T2 new_dist) {
		//new_dist -= min_offset;
		if (new_dist < KEY_THRESHOLD) {
			// 小于的时候就插入到数组中
			auto& v = v_dist[new_dist];
			if (!v.empty()) {
				v.emplace_back(id);
			}
			else {
				v.emplace_back(id);
				Q_set.push(new_dist);
			}
		}
		else {
			auto it = map_dist.find(new_dist);

			if (it != map_dist.end()) {
				it->second.emplace_back(id);
			}
			else {
				map_dist[new_dist].emplace_back(id);
				Q_set.push(new_dist);
			}
		}
	}

	inline void clear() {
		map_dist.clear();
	}

	inline bool empty() {
		return Q_set.empty();
	}

	inline std::vector<uint32>& pop(T2& top_dist) {

		top_dist = Q_set.top();
		Q_set.pop();

		if (top_dist < KEY_THRESHOLD) {
			return v_dist[top_dist];
		}
		else {
			return map_dist[top_dist];
		}
	}
};

/**
 * 迪杰斯特拉算法类，每一个线程用一个
 */
template <class T>
struct Thread_DIJ
{

	uint32 S_set[MAX_NODES];				// 记录当前节点已经找到的最短路径的终点的集合
	uint32 used_pre[MAX_RECORDS];			// 前置节点列表
	//Info val_info[MAX_NODES];				// sigma值和delta值
	Dis dis_set[MAX_NODES];					// 节点信息列表
	T weight[MAX_NODES];					// 当前最短路径的权重

	//uint32	sigma_bak[MAX_NODES];			// sigma值->最短路径的条数相关
	double	delta[MAX_NODES];				// delta值->当前处理节点所产生的centrality
	double centrality[MAX_NODES];			// 当前线程累积处理的所有节点所产生的centrality

	_edge_T forwardG[MAX_RECORDS];         // 图，用一维前向星结构存储
	int head_next[MAX_NODES];		// 图相关，记录每一个节点的邻接点在图中的位置

	VMap<uint32, T> vmap;

#ifdef IS_DEBUG_MODE
	// 给程序计时所用
	Timer t0, t1, t2;
	uint64 cnt1, cnt2, cnt3;
#endif
};
Thread_DIJ<uint64>* dij_threads_int64[NUM_THREADS];
Thread_DIJ<uint32>* dij_threads_int32[NUM_THREADS];

/*
* =====================================================================================
* DIJ 的算法，做一次. 找到begin到其它所有点的最短路径
* =====================================================================================
*/
template <class T>
void run_one_node(const uint32 begin, Thread_DIJ<T>& pthred) {

	/**
	 * --------------------------------------------------------------------------------
	 * 特殊情况无需处理
	 * --------------------------------------------------------------------------------
	 */
	if (begin >= n_nodes || total_special_node_flag[begin] == 1) {
		return;
	}

	/**
	 * --------------------------------------------------------------------------------
	 * 获取当前线程需要处理的变量
	 * --------------------------------------------------------------------------------
	 */
	int n_min = 0;													// 记录当前起点可以到达的终点的个数
	double* centrality = pthred.centrality;				// 当前线程累积处理的所有节点所产生的centrality
	//Info* val_info = pthred.val_info;						// 当前处理节点所产生的centrality
	uint32* S_set = pthred.S_set;								// 记录当前节点已经找到的最短路径的终点的集合
	Dis* dis_set = pthred.dis_set;						// 节点信息列表
	uint32* used_pre = pthred.used_pre;						// 前置节点列表
	T* weight = pthred.weight;
	//uint32* sigma_bak = pthred.sigma_bak;
	double* delta = pthred.delta;
	_edge_T* forwardG = pthred.forwardG;
	int* head_next = pthred.head_next;

#ifdef IS_DEBUG_MODE
	// 给程序计时所用
	Timer& t0 = pthred.t0;
	Timer& t1 = pthred.t1;
	Timer& t2 = pthred.t2;
	uint64& cnt1 = pthred.cnt1;
	uint64& cnt2 = pthred.cnt2;
	uint64& cnt3 = pthred.cnt3;
#endif
	/**
	 * --------------------------------------------------------------------------------
	 * 初始化当前线程对应的结构体信息 （计算新起点的最短路径时，需要先初始化）
	 * --------------------------------------------------------------------------------
	 */
	 //map_dist.clear();			// 清空map
	auto& vmap = pthred.vmap;
	vmap.clear();

	// 设置起点相关信息
	//dis_set[begin].visit = true;
	dis_set[begin].sigma = 1;
	weight[begin] = 0;
	S_set[n_min++] = begin;

	//uint64 min_dist = LLONG_MAX;
	/*for (int i = head_next[begin].first, j = head_next[begin].second; i < j; i++) {
		auto& edge = forwardG[i];
		min_dist = min_dist > edge.money ? edge.money : min_dist;
	}*/
	vmap.set_min_offset(0);

	for (int i = head_next[begin], j = head_next[begin + 1]; i < j; i++) {
		auto& edge = forwardG[i];
		//insert(map_dist, Q_set, edge.to, edge.money);
		vmap.insert(edge.to, edge.money);

		auto& idis = dis_set[edge.to];
		//idis.weight = edge.money;
		weight[edge.to] = edge.money;
		idis.sigma = 1;
		idis.n_used = 1;
		used_pre[idis.pre_start] = 0;
	}

	/**
	 * --------------------------------------------------------------------------------
	 * 开始寻找以begin为起点到其它所有点的最短路径
	 * --------------------------------------------------------------------------------
	 */

#ifdef IS_DEBUG_MODE
	t1.reset();
#endif
	// 优先队列里面只存储dist，重复的dist被放到一个vector中
	//while (!Q_set.empty()) {
	while (!vmap.empty()) {

		//uint64 top_dist = Q_set.top();
		//Q_set.pop();

		// 处理当前最短路径对应的所有的id map的key为dist，value为id值
		//auto& v = map_dist[top_dist];
		T top_dist;
		auto& v = vmap.pop(top_dist);


		for (auto& top_id : v) {

			const auto now_min_weight = weight[top_id];

			if (top_dist == now_min_weight) {

				auto& cur_dis = dis_set[top_id];

				//sigma_bak[n_min] = cur_dis.sigma;
				S_set[n_min++] = top_id;
				//cur_dis.visit = true;

				const auto end = head_next[top_id + 1];
				for (int i = head_next[top_id]; i < end; i++) {
					const auto& edge = forwardG[i];
					const auto to = edge.to;
					auto& weight_to = weight[to];

					const T new_weight = now_min_weight + edge.money;

					// 新距离并不比现在的距离小，就直接跳过
#ifdef LINUX_SYSTEM
					if (likely(new_weight > weight_to)) {
#else
					if ((new_weight > weight_to)) {
#endif
						continue;
					}
					else if (new_weight < weight_to) {
						auto& idis = dis_set[to];

						weight_to = new_weight;
						idis.sigma = cur_dis.sigma;

						idis.n_used = 1;
						used_pre[idis.pre_start] = n_min - 1;

						//insert(map_dist, Q_set, edge.to, new_weight);
						vmap.insert(to, new_weight);
					}
					else {
						auto& idis = dis_set[to];

						idis.sigma += cur_dis.sigma;
						used_pre[idis.pre_start + idis.n_used++] = n_min - 1;
					}

				}
			}
		}

		// 清空当前处理过的vector
		v.clear();
	}

#ifdef IS_DEBUG_MODE
	t1.add();
	t2.reset();
#endif

	/**
	 * --------------------------------------------------------------------------------
	 * 根据计算得到的结果更新每一个节点的centrality的值
	 * --------------------------------------------------------------------------------
	 */
	int coef = 1;
	if (total_special_node_flag[begin] > 1) {
		coef = total_special_node_flag[begin];
		centrality[begin] += (n_min - 1) * (coef - 1);
	}

	/**
	 * 利用新公式
	 */
	while (--n_min > 0) {
		auto& iw = S_set[n_min];
		Dis& w = dis_set[iw];

		double dv = delta[n_min] + 1.0 / (double)w.sigma;

		const auto end = w.pre_start + w.n_used;
		for (int i = w.pre_start; i < end; i++) {
			delta[used_pre[i]] += dv;
		}

		centrality[iw] += delta[n_min] * w.sigma * coef;
		w.reset();
		weight[iw] = -1;
		delta[n_min] = 0;
	}

	dis_set[begin].reset();
	weight[begin] = -1;
	delta[0] = 0;
#ifdef IS_DEBUG_MODE
	t2.reset();
#endif
}


/**
 * =====================================================================================
 * DIJ 结构体的初始化
 * =====================================================================================
 */
template <class T>
void initial(int pid, Thread_DIJ<T>*& ptr) {
	ptr = new Thread_DIJ<T>();
	auto& idij = *ptr;

	int offset = 0;
	for (int i = 0; i < n_nodes; i++) {
		auto& idis = idij.dis_set[i];

		idis.pre_start = offset;

		offset += degrees[i].in_degree;
		idis.reset();
		idij.weight[i] = (T)-1;

	}
	memset(idij.centrality, 0, sizeof(double) * n_nodes);
	memset(idij.used_pre, 0, sizeof(uint32) * n_records);
	memset(idij.delta, 0, sizeof(double) * n_nodes);

	// 拷贝退
	memcpy(idij.head_next, total_head_next, sizeof(uint32) * (n_nodes+1));
	memcpy(idij.forwardG, total_forwardG, sizeof(_edge_T) * n_records);
	//memset(idij.sigma_bak, 0, sizeof(uint32) * n_nodes);
	//memset(idij.val_info, 0, sizeof(Info) * n_nodes);
	//memset(idij.weight, -1, sizeof(T) * n_nodes);
}

/**
 * 打印结果信息
 */
#ifdef  IS_DEBUG_MODE
template <class T>
void print_iter_info(const int igroup, Thread_DIJ<T>& pthred) {

	// 打印进度信息
	char tmp[1000];
	int interval;

	if (n_nodes > 10000) {
		interval = n_group / NPRINT_PER_NG;
		if (interval > 0 && igroup % interval == 0) {
			sprintf(tmp, "%d%% [%d/%d] [cnt1:%1:cnt2:%d]", int(igroup * 1.0 / n_group * 100),
				igroup, n_group, pthred.cnt1, pthred.cnt2);
			pthred.t0.stop(tmp);
			pthred.t1.print("Find Path");
			pthred.t2.print("Calculate Centrality");
		}
	}
}
#endif

/**
 * 处理一个组的节点
 */
void run_one_group_int64(const int& igroup, const int pid) {

	auto& info = groups[igroup];

	//std::cout << igroup << std::endl;
	auto& idij = *(dij_threads_int64[pid]);

	for (int i = info.start; i < info.end; i++) {
		run_one_node(i, idij);
	}

#ifdef  IS_DEBUG_MODE
	print_iter_info(igroup, dij_threads_int64[pid]);
#endif
}

inline void run_one_group_int32(const int& igroup, const int pid) {

	auto& info = groups[igroup];
	auto& idij = *(dij_threads_int32[pid]);

	for (uint32 i = info.start; i < info.end; i++) {
		run_one_node(i, idij);
	}

#ifdef  IS_DEBUG_MODE
	print_iter_info(igroup, dij_threads_int32[pid]);
#endif
}

/**
 * =====================================================================================
 * 开启每一个线程
 * =====================================================================================
 */
std::mutex mtx;
std::vector<bool> has_done;
int cur_group = 0;

void run_one_thread(int pid) {

	int group_id = 0;

	switch (data_type_flag) {
	case 64:
		// 首先给结构体初始化
		initial(pid, dij_threads_int64[pid]);

		// 根据抢占式来并行处理每一个节点
		while (true) {
			{
				std::lock_guard<std::mutex> lk(mtx);
				if (cur_group < n_group) {
					group_id = cur_group++;
				}
				else {
					break;
				}
			}

			run_one_group_int64(group_id, pid);
		}
	case 32:
		// 首先给结构体初始化
		initial(pid, dij_threads_int32[pid]);

		// 根据抢占式来并行处理每一个节点
		while (true) {
			{
				std::lock_guard<std::mutex> lk(mtx);
				if (cur_group < n_group) {
					group_id = cur_group++;
				}
				else {
					break;
				}
			}

			run_one_group_int32(group_id, pid);
		}

		break;
	}
}

/**
 * 用多线程计算所有节点的centrality
 */
void calculate_all_centrality() {


#ifdef  IS_DEBUG_MODE
	Timer t;
	printf("\n");
#endif

	// 初始化centrality的值
	memset(centrality, 0, sizeof(_centraility) * n_nodes);

	//i_group.store(0);
	has_done.resize(n_nodes, false);
	cur_group = 0;

	// 开始给线程分组
	int nk = 0;			// 跑多少个点，测试时只跑部分点
#ifndef LINUX_SYSTEM

	if (n_nodes < 80000 && n_nodes > 10000) {
		nk = 1000;
	}
	else {
		nk = 10000;
	}
	if (nk > n_nodes) {
		nk = n_nodes;
	}
#else
	nk = n_nodes;
#endif

	n_group = nk / SIZE_GROUP;

	groups.resize(n_group);
	split_to_blocks(n_nodes, n_group, groups.data());

	//i_group.store(0, std::memory_order_relaxed);

	// calculate centrality by threads
	std::thread ts[NUM_THREADS];
	for (int i = 0; i < NUM_THREADS; i++) {
		ts[i] = std::thread(&run_one_thread, i);
	}

	for (int i = 0; i < NUM_THREADS; i++)    ts[i].join();

#ifdef  IS_DEBUG_MODE
	t.stop("Calculate");
#endif
}

/**
 * 将所有的centrality加起来
 */
void sum_all_centrality() {
#ifdef  IS_DEBUG_MODE
	Timer t;
#endif

	switch (data_type_flag) {
	case 64:
		

		for (int i = 0; i < ALL_NUM_THREADS; i++) {
			auto& icentrality = dij_threads_int64[i]->centrality;

			for (int j = 0; j < n_nodes; j++) {
				centrality[j].node = map_to_org[new_map_to_org[j]];
				centrality[j].value += icentrality[j];
			}
		}
		break;
	case 32:
		// 首先给结构体初始化
		for (int i = 0; i < ALL_NUM_THREADS; i++) {
			auto& icentrality = dij_threads_int32[i]->centrality;

			for (int j = 0; j < n_nodes; j++) {
				centrality[j].node = map_to_org[new_map_to_org[j]];
				centrality[j].value += icentrality[j];
			}
		}
		break;
	}


	std::sort(centrality, centrality + n_nodes, [](const _centraility& item1, const _centraility& item2) {
		if (abs(item1.value - item2.value) <= 0.0001) {
			return item1.node < item2.node;
		}
		else {
			return item1.value > item2.value;
		}
		});

#ifdef  IS_DEBUG_MODE
	t.stop("Sum");
#endif

}

/**
 * 将结果写到文件中
 */
void write_topn_centrality(const std::string& result_file) {
#ifdef  IS_DEBUG_MODE
	Timer t;
#endif

	std::ofstream out(result_file);

	if (out.fail()) {
		printf("保存结果文件失败!\n");
		exit(0);
	}

	for (int i = 0; i < TOP_N; i++) {
		//fwrite("");
		auto& item = centrality[i];
		out << item.node << "," << std::fixed << std::setprecision(3) << item.value << std::endl;
	}

	out.close();

#ifdef  IS_DEBUG_MODE
	t.stop("Write");
#endif

}

/**
 * 主函数
 */
void main_one_piece(const std::string& test_data_file, const std::string& result_data_file)
{
#ifdef  IS_DEBUG_MODE
	Timer t;
	std::cout << std::endl << "Size of long long is " << sizeof(uint64) << std::endl;
#endif

	Graph graph;
	graph.load_data(test_data_file);


	calculate_all_centrality();

	sum_all_centrality();

	write_topn_centrality(result_data_file);

	// 清空内存
	if (data_type_flag == 32) {
		for (int i = 0; i < NUM_THREADS; i++) {
			delete dij_threads_int32[i];
		}
		
	}
	else {
		for (int i = 0; i < NUM_THREADS; i++) {
			delete dij_threads_int64[i];
	}
	}

#ifdef  IS_DEBUG_MODE
	t.stop("Total");
#endif
}

// 调用diff命令判断两个结果是否相同
void judge(const std::string& file1, const std::string& file2) {
	char buff[1000];
	sprintf(buff, "diff %s %s -q", file1.c_str(), file2.c_str());
	system(buff);
}

int main(int argc, char* argv[])
{
	bool is_debug_mode = argc >= 2 && strlen(argv[1]) >= 1;
	if (is_debug_mode) {
		// 通过输入参数来测试多个数据集
		for (int i = 0; i < argc - 1; ++i) {
			printf("Test%d: %s\t", i + 1, argv[i + 1]);
			char buff[1000];
			sprintf(buff, "./data/%s/data%s.txt", argv[i + 1], argv[i + 1]);
			std::string test_data_file = buff;
			sprintf(buff, "./data/%s/result.txt", argv[i + 1]);
			std::string result_data_file = buff;
			sprintf(buff, "./data/%s/result%s.txt", argv[i + 1], argv[i + 1]);
			std::string answer_data_file = buff;

			sprintf(buff, "rm ./data/%s/result.txt", argv[i + 1]);
			system(buff);

			n_nodes = 0;										// 节点个数
			n_records = 0;

			main_one_piece(test_data_file, result_data_file);
			judge(result_data_file, answer_data_file);
			printf("\n");
		}
	}
	else {
		std::string test_data_file = "/data/test_data.txt";
		std::string result_data_file = "/projects/student/result.txt";

		main_one_piece(test_data_file, result_data_file);
	}

	exit(0);
}

