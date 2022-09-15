#include<iostream>
#include<cstdio>
#include<map>
#include<vector>
#include<string>
#include<algorithm>
#include<queue>
using namespace std;
typedef int LL;
typedef pair<int, int> pp;
const int maxn = 107, maxw = 107, maxd = 1007, maxe = 1007;
LL N, K[maxn], R, L, W, D, E, F[maxn], T;
int area_id[maxn * 5], area_energy_type[maxn * 5];//车间区域属性
LL window_looptype1;//第一种环回窗口数量
LL fabric_time[5];//五种资源加工时间;
bool loop_mark,loop_mark1;
bool self_loop[maxw];//是否自回环
bool mark_zero[maxd];
LL window_id[maxw], window_cost_coef[maxw], window_workshop[maxw];//窗口属性
LL window_fabric[maxw][4];//窗口预加工
LL apparatus_type[maxd], apparatus_applicost[maxd][5];//仪器属性
LL apparatus_energy[3][2] = { {0,1},{0,2} ,{3,4} };//仪器种类对应能源种类；
vector<int>window_area[maxw];//窗口对应的车间区域
vector<int>workshop_window[maxn];//车间区域对应的窗口
vector<int >workshop_area[maxn];//车间包含区域
struct Edge {
	int id, etype;
	int from, to;
	Edge(int id_, int type_, int from_, int to_) {
		id = id_, from = from_, to = to_, etype = type_;
	}
};
vector<Edge>edge_graph;//流水图（正向）
vector<Edge>edge_graph_rev;//流水图（反向）
vector<int>edge_line[20];
int re_install_cnt[maxd];
bool edge_line_mark[maxd], edge_line_mark0[maxd], edge_line_mark1[maxd][20];
vector<pp>apparatus_graph[maxd];
vector<pp>rev_apparatus_graph[maxd];
LL loop_times[maxw];//以窗口w为出发点的回环次数
LL vis_times[maxw];//窗口w经过次数；

LL prefab_cnt[maxd];//仪器前驱安装情况

struct install_status {
	int id = 0;
	int window =0;
	int area = 0;
	int pre_window = 0;
	int nxt_window = 0;
	int mark = 0;
	int mark1 = 0;
	int loop_times[maxw];
	int vis_times[maxw];
	install_status() {
		id = 0;
		window = -1;
		area = -1;
		pre_window = -1;
		mark = 0;
		mark1 = 0;
		for (int i = 0; i < W; i++)loop_times[i] = vis_times[i]=0;
	}
	install_status(int id_, int pre_window_) {
		id = id_;
		pre_window = pre_window_;
		for (int i = 0; i < W; i++)loop_times[i] = vis_times[i] = 0;
	}
};
install_status apparatus_status[maxd];
void copy_loop_times(int app_a, int app_b,int mark) {//a为b的前驱
	
	int prewindow = apparatus_status[app_b].pre_window;
	int nowwindow = apparatus_status[app_a].window;
	if (nowwindow < window_looptype1 && prewindow < window_looptype1) {
		if (apparatus_status[app_a].loop_times[window_looptype1-1] == apparatus_status[app_b].loop_times[window_looptype1-1]) {
			if (nowwindow > prewindow) {
				apparatus_status[app_b].pre_window = nowwindow;
				apparatus_status[app_b].mark = mark;
			}
			else if (nowwindow == prewindow) {
				apparatus_status[app_b].mark = min(apparatus_status[app_b].mark, mark);
			}
		}
		else if (apparatus_status[app_a].loop_times[window_looptype1-1] > apparatus_status[app_b].loop_times[window_looptype1-1]) {
			apparatus_status[app_b].pre_window = nowwindow;
			apparatus_status[app_b].mark = mark;
		}
	}
	else if (nowwindow == prewindow) {
		if (apparatus_status[app_a].loop_times[nowwindow] == apparatus_status[app_b].loop_times[nowwindow]) {
			apparatus_status[app_b].mark = min(apparatus_status[app_b].mark, mark);
		}
		else if (apparatus_status[app_a].loop_times[nowwindow] > apparatus_status[app_b].loop_times[nowwindow]) {
			apparatus_status[app_b].pre_window = nowwindow;
			apparatus_status[app_b].mark = mark;
		}
	}
	else if (nowwindow > prewindow) {
		apparatus_status[app_b].pre_window = nowwindow;
		apparatus_status[app_b].mark = mark;
	}
	for (int i = 0; i < W; i++) {
		apparatus_status[app_b].loop_times[i] = max(apparatus_status[app_b].loop_times[i], apparatus_status[app_a].loop_times[i]);
		//apparatus_status[app_b].vis_times[i] = max(apparatus_status[app_b].vis_times[i], apparatus_status[app_a].vis_times[i]);
		//apparatus_status[app_b].loop_times[i] = 0;
	}
}

void rev_copy(int app_id) {//回溯窗口loop状态
	loop_mark = 0;
	for (int i = 0; i < W; i++) {
		loop_times[i] = apparatus_status[app_id].loop_times[i];
		//vis_times[i] = apparatus_status[app_id].vis_times[i];
	}
}

void fore_copy(int app_id) {
	for (int i = 0; i < W; i++) {
		apparatus_status[app_id].loop_times[i] = loop_times[i];
		//apparatus_status[app_id].vis_times[i] = vis_times[i];
	}
}

bool install_dfs(int app_id, int now_window) {//寻找次此安装区域/窗口a
	if (now_window < 0)while (1);
	int now_flag;
	LL app_ty = apparatus_type[app_id];
	LL e_ty1 = apparatus_energy[app_ty][0], e_ty2 = apparatus_energy[app_ty][1];
	if (window_fabric[now_window][app_ty] == 0 && edge_line_mark0[app_id]) {
		now_flag = 0;
	}
	else if (window_fabric[now_window][app_ty]  && edge_line_mark0[app_id]) {
		now_flag = 2;
	}
	else {
		now_flag = 1;
	}
	//vis_times[now_window]++;
	if (now_flag) {//当前窗口能进行预加工
		int se_ = window_area[now_window].size();
		LL mincost = -1;
		int install_area = -1;
		for (int i = 0; i < se_; i++) {//安装仪器至当前窗口
			int a_id = window_area[now_window][i];
			int en_type = area_energy_type[a_id];
			if (e_ty1 == en_type || e_ty2 == en_type) {
				if (install_area == -1) {
					mincost = apparatus_applicost[app_id][en_type];
					mincost += window_cost_coef[now_window] * fabric_time[en_type] * (now_flag - 1);
					install_area = a_id;
				}
				else if (apparatus_applicost[app_id][en_type] + window_cost_coef[now_window] * fabric_time[en_type] * (now_flag - 1) < mincost) {
					mincost = apparatus_applicost[app_id][en_type];
					mincost += window_cost_coef[now_window] * fabric_time[en_type] * (now_flag - 1);
					install_area = a_id;
				}
				
			}
		}
		if (install_area != -1) {
			apparatus_status[app_id].window = now_window;
			apparatus_status[app_id].area =install_area;
			loop_mark=loop_mark1 = 0;
			return true;
		}
	}
	if (now_window == window_looptype1 - 1) {//1类回环尝试
		if (loop_mark == 1) {
			vis_times[now_window]--;
			return false;
		}
		if (loop_times[now_window] < L) {
			if (edge_line_mark0[app_id])loop_times[now_window]++;
			//loop_times[now_window]++;
			loop_mark = 1;
			if (install_dfs(app_id, 0)) {
				loop_mark = 0;
				return true;
			}
			else {
				
				if (edge_line_mark0[app_id])loop_times[now_window]--;
				//loop_times[now_window]++;
				loop_mark = 0;
			}
		}
	}
	if (now_window +1 >= W)return false;
	if (install_dfs(app_id, now_window + 1)) {
		return true;
	}
	else {
		
		return false;
	}
}


void install(int app_id, int pre_window) {
	int now_flag = 0;
	if (mark_zero[app_id]) { 
		if(install_dfs(app_id, 0))return;
		pre_window = 0;
	}
	else if (apparatus_status[app_id].mark) {
		if (install_dfs(app_id, pre_window))return;
	}
	LL app_ty = apparatus_type[app_id];
	LL e_ty1 = apparatus_energy[app_ty][0], e_ty2 = apparatus_energy[app_ty][1];
	if (window_fabric[pre_window][app_ty] == 0 && edge_line_mark0[app_id]) {
		now_flag = 0;
	}
	else if(window_fabric[pre_window][app_ty]  && edge_line_mark0[app_id]){
		now_flag = 2;
	}
	else {
		now_flag = 1;
	}
	if (self_loop[pre_window]&&loop_times[pre_window] < L &&now_flag) {//判断能否自回环安装
		LL mincost = -1;
		int install_area = -1;
		int se_ = window_area[pre_window].size();
		for (int i = 0; i < se_; i++) {//安装仪器至当前窗口
			int a_id = window_area[pre_window][i];
			int en_type = area_energy_type[a_id];
			if (e_ty1 == en_type || e_ty2 == en_type) {
				if (install_area == -1) {
					mincost = apparatus_applicost[app_id][en_type];
					mincost += window_cost_coef[pre_window] * fabric_time[en_type] * (now_flag - 1);
					install_area = a_id;
				}//安装费用+窗口（资源）加工费用
				else if (apparatus_applicost[app_id][area_energy_type[a_id]] + window_cost_coef[pre_window] * fabric_time[en_type] * (now_flag - 1) < mincost) {
					mincost = apparatus_applicost[app_id][area_energy_type[a_id]];
					mincost += window_cost_coef[pre_window] * fabric_time[en_type] * (now_flag - 1);
					install_area = a_id;
				}

			}
		}
		if (install_area != -1) {
			apparatus_status[app_id].window = pre_window;
			apparatus_status[app_id].area = install_area;
			loop_mark=loop_mark1 = 0;
			if (edge_line_mark0[app_id])loop_times[pre_window]++;
			//loop_times[pre_window]++;
			//vis_times[pre_window]++;
			return;
		}
	}
	else if (loop_times[pre_window] < L && pre_window == window_looptype1 - 1&&loop_mark==0) {
		loop_mark = 1;
		if(edge_line_mark0[app_id])loop_times[pre_window]++;
		//loop_times[pre_window]++;
		if (install_dfs(app_id, 0)) {
			loop_mark = 0;
			return;
		}
		else {
			loop_mark = 0;
			if (edge_line_mark0[app_id])loop_times[pre_window]--;
			//loop_times[pre_window]++;
		}
	}
	if (pre_window + 1 >= W)return;
	install_dfs(app_id, pre_window + 1);
}

void install_bfs() {
	queue<int>que;
	for (int i = 0; i < D; i++) {//将没有前置加工的仪器入队
		apparatus_status[i].id = i;
		if (prefab_cnt[i] == 0) {
			mark_zero[i] = 1;
			que.push(i);
		}
	}
	while (!que.empty()) {
		int now_app_id = que.front();
		que.pop();
		rev_copy(now_app_id);
		install(now_app_id, apparatus_status[now_app_id].pre_window);
		fore_copy(now_app_id);
		int se_ = apparatus_graph[now_app_id].size();
		for (int i = 0; i < se_; i++) {
			pp nxt_app = apparatus_graph[now_app_id][i];
			int nxt_app_id = nxt_app.first;
			prefab_cnt[nxt_app_id]--;//更新前置窗口，使其最大化
			copy_loop_times(now_app_id, nxt_app_id, edge_graph[nxt_app.second].etype);
			
			if (!prefab_cnt[nxt_app_id]) {//前置仪器加载完成即可入队
				que.push(nxt_app_id);
			}
		}
	}
}

bool re_install_push_back(int app_id, int now_window, int max_window) {
	if (apparatus_status[app_id].mark1)return false;
	int now_flag;
	LL app_ty = apparatus_type[app_id];
	LL e_ty1 = apparatus_energy[app_ty][0], e_ty2 = apparatus_energy[app_ty][1];
	re_install_cnt[app_id] = 1;
	if (window_fabric[now_window][app_ty] == 0 && edge_line_mark0[app_id]) {
		now_flag = 0;
	}
	else if (window_fabric[now_window][app_ty] && edge_line_mark0[app_id]) {
		now_flag = 2;
	}
	else {
		now_flag = 1;
	}
	//vis_times[now_window]++;
	if (now_flag==1) {
		if (now_window == max_window&&apparatus_status[app_id].window!=now_window) {
			if (loop_times[now_window] < L&& now_window != window_looptype1 - 1) {
				loop_mark = 1;
				loop_times[now_window]++;
			}
			else {
				return false;
			}
			
			return false;
		}
		else if (now_window < max_window) {
			if (re_install_push_back(app_id, now_window + 1, max_window)) {
				return true;
			}
		}
		else if (now_window == apparatus_status[app_id].window) {
			return false;
		}
		int o_a_id = apparatus_status[app_id].area;
		int o_window = apparatus_status[app_id].window;
		int o_en_type = area_energy_type[o_a_id];
		LL origin_cost = apparatus_applicost[app_id][o_en_type];
		int se_ = window_area[now_window].size();
		LL mincost = -1;
		int install_area = -1;
		for (int i = 0; i < se_; i++) {//安装仪器至当前窗口
			int a_id = window_area[now_window][i];
			int en_type = area_energy_type[a_id];
			if (e_ty1 == en_type || e_ty2 == en_type) {
				if (install_area == -1) {
					mincost = apparatus_applicost[app_id][en_type];
					install_area = a_id;
				}
				else if (apparatus_applicost[app_id][area_energy_type[a_id]] + window_cost_coef[now_window] * fabric_time[en_type] * (now_flag - 1) < mincost) {
					mincost = apparatus_applicost[app_id][area_energy_type[a_id]];
					install_area = a_id;
				}

			}
		}
		if (install_area != -1) {
			int en_type = area_energy_type[install_area];
			//mincost += fabric_time[en_type] * K;
			if (mincost > origin_cost) {
				if (loop_mark == 1)loop_times[now_window]--;
				return false;
			}
			apparatus_status[app_id].window = now_window;
			apparatus_status[app_id].area = install_area;
			loop_mark = 0;
			return true;
		}
		else {
			if (loop_mark == 1)loop_times[now_window]--;
		}
		return false;
	}
	
	if (now_flag == 2) {
		int o_a_id =apparatus_status[app_id].area;
		int o_window = apparatus_status[app_id].window;
		int o_en_type = area_energy_type[o_a_id];
		LL origin_cost = window_cost_coef[o_window] * fabric_time[o_en_type];
		LL kk = 0;
		for (int t = 0; t < T; t++) {
			if (edge_line_mark1[app_id][t]) {
				kk += K[t];
			}
		}
		origin_cost += fabric_time[o_en_type] * kk+ apparatus_applicost[app_id][o_en_type];
		if (now_window == max_window && apparatus_status[app_id].window != now_window) {
			/*if (loop_times[now_window] < L && now_window != window_looptype1 - 1) {
				loop_mark = 1;
				loop_times[now_window]++;
			}
			else {
				return false;
			}*/
			return false;
		}
		else if (now_window < max_window) {
			if (re_install_push_back(app_id, now_window + 1, max_window)) {
				return true;
			}
		}
		else if (now_window == apparatus_status[app_id].window) {
			return false;
		}

		int se_ = window_area[now_window].size();
		LL mincost = -1;
		int install_area = -1;
		for (int i = 0; i < se_; i++) {//安装仪器至当前窗口
			int a_id = window_area[now_window][i];
			int en_type = area_energy_type[a_id];
			if (e_ty1 == en_type || e_ty2 == en_type) {
				if (install_area == -1) {
					mincost = apparatus_applicost[app_id][en_type];
					install_area = a_id;
				}
				else if (apparatus_applicost[app_id][area_energy_type[a_id]] + window_cost_coef[now_window] * fabric_time[en_type] * (now_flag - 1) < mincost) {
					mincost = apparatus_applicost[app_id][area_energy_type[a_id]];
					install_area = a_id;
				}

			}
		}
		if (install_area != -1) {
			int en_type = area_energy_type[install_area];

			mincost+= fabric_time[en_type] * kk;
			if (mincost > origin_cost) { 
				if (loop_mark == 1)loop_times[now_window]--;
				return false;
			}
			apparatus_status[app_id].window = now_window;
			apparatus_status[app_id].area = install_area;
			loop_mark = 0;
			return true;
		}
		else {
			if (loop_mark == 1)loop_times[now_window]--;
		}
		return false;

	}
	return false;
}


bool re_install_dfs(int app_id) {
	int se_ = apparatus_graph[app_id].size();
	int max_win = W;
	for (int i = 0; i < se_; i++) {
		pp nxt_app = apparatus_graph[app_id][i];
		int nxt_app_id = nxt_app.first;
		if (!re_install_cnt[nxt_app_id])re_install_dfs(nxt_app_id);
		//re_install_dfs(nxt_app_id);
		if (edge_graph[nxt_app.second].etype && max_win > apparatus_status[nxt_app_id].window)apparatus_status[app_id].mark1 = apparatus_status[nxt_app_id].mark1 = 1;
		else if(max_win > apparatus_status[nxt_app_id].window){
			apparatus_status[app_id].mark1 = min(apparatus_status[app_id].mark1, edge_graph[nxt_app.second].etype);
		}
		max_win = min(max_win, apparatus_status[nxt_app_id].window);
		
	}

	int origin_window = apparatus_status[app_id].window;
	return re_install_push_back(app_id, origin_window + 1, max_win);
}

void re_install(){
	int first_re_install = -1;
	for (int i = 0; i < D; i++) {
		if (edge_line_mark0[i]) {
			int flag = 1;
			for (auto pre : rev_apparatus_graph[i]) {
				if (edge_line_mark0[pre.first]) {
					flag = 0;
					break;
				}
			}
			if (flag) {
				first_re_install = i;
				break;
			}
		}
	}
	re_install_dfs(first_re_install);
}


void read_window_info() {
	//cin >> K;//生产次数
	for (int i = 0; i < 5; i++)cin >> fabric_time[i];//5种资源加工时间
	cin >> N;//车间数量
	cin >> R;//区域数量
	for (int i = 0; i < R; i++) {
		cin >> area_id[i];//区域对应车间
		cin >> area_energy_type[i];//区域能源类型
		workshop_area[area_id[i]].push_back(i);
	}
	cin >> L;//环回圈数
	cin >> window_looptype1;//第一种环回窗口数量
	cin >> W;//窗口数量
	for (int i = 0; i < W; i++) {
		cin >> self_loop[i];
		cin >> window_id[i];//对应车间下标
		cin >> window_cost_coef[i];
		for (int j = 0; j < 3; j++) {
			cin >> window_fabric[i][j];
		}
		workshop_window[window_id[i]].push_back(i);
		int se_ = workshop_area[window_id[i]].size();
		for (int j = 0; j < se_; j++) {
			int app_id = workshop_area[window_id[i]][j];
			window_area[i].push_back(app_id);//建立窗口-区域连接
		}
	}
}

void read_apparatus() {
	cin >> D;//仪器数量
	for (int i = 0; i < D; i++) {
		cin >> apparatus_type[i];
		for (int j = 0; j < 5; j++) {
			cin >> apparatus_applicost[i][j];
		}
	}
	cin >> E;//流水图边数
	for (int i = 0; i < E; i++) {
		int edge_type, from, to;
		cin >> edge_type >> from >> to;
		edge_graph.push_back(Edge(i, edge_type, from, to));
		apparatus_graph[from].push_back(pp{ to,i });
		rev_apparatus_graph[to].push_back(pp{ from,i });
		re_install_cnt[from]++;
		prefab_cnt[to]++;
	}
	cin >> T;
	for (int t = 0; t < T; t++) {
		cin >> K[t];
		cin >> F[t];//流水线
		for (int i = 0; i < F[t]; i++) {
			int ed_id;
			cin >> ed_id;
			edge_line[t].push_back(ed_id);
			int f1 = edge_graph[ed_id].from;
			int f2 = edge_graph[ed_id].to;
			edge_line_mark0[f1] = 1;
			edge_line_mark1[f1][t] = 1;
			edge_line_mark0[f2] = 1;
			edge_line_mark1[f2][t] = 1;
		}
	}
}


void output() {
	cout << D << "\n";
	for (int i = 0; i < D; i++) {
		//if (apparatus_status[i].area == -1)apparatus_status[i].area = 0;
		//if (apparatus_status[i].area == -1)while (1);
		if (i < D - 1) {
			
			cout << apparatus_status[i].area << " ";
		}
		else cout << apparatus_status[i].area << "\n";

	}
	cout << T << "\n";
	for (int t = 0; t < T; t++) {
		int cnt = 0;
		int cnt2 = 0;
		for (int i = 0; i < D; i++) { 
			edge_line_mark[i] = 0;
			if (edge_line_mark1[i][t])cnt++;
		}
		cout << cnt << " ";
		for (auto ed : edge_line[t]) {
			int f1 = edge_graph[ed].from;
			int f2 = edge_graph[ed].to;
			if (!edge_line_mark[f1]) {
				//if (apparatus_status[f1].window == -1)apparatus_status[f1].window = 0;
				//if (apparatus_status[f1].window == -1)while (1);
				cnt2++;
				if (cnt2 == cnt)
					cout << apparatus_status[f1].window;
				else cout << apparatus_status[f1].window << " ";
				edge_line_mark[f1] = 1;

			}
			if (!edge_line_mark[f2]) {
				//if (apparatus_status[f2].window == -1)apparatus_status[f2].window = 0;
				//if (apparatus_status[f1].window == -1)while (1);
				cnt2++;
				if (cnt2 == cnt)
					cout << apparatus_status[f2].window;
				else cout << apparatus_status[f2].window << " ";
				edge_line_mark[f2] = 1;
			}
		}
		if (t < T - 1)cout << "\n";
	}
}


void test() {
	for (int app_id = 0; app_id < D; app_id++) {
		LL app_ty = apparatus_type[app_id];
		LL e_ty1 = apparatus_energy[app_ty][0], e_ty2 = apparatus_energy[app_ty][1];
		for (int j = W-1; j>=0; j--) {
			int se_ = window_area[j].size();
			int install_area = apparatus_status[app_id].area;
			for (int i = 0; i < se_; i++) {//安装仪器至当前窗口
				int a_id = window_area[j][i];
				int en_type = area_energy_type[a_id];
				if (e_ty1 == en_type || e_ty2 == en_type) {
					if (install_area == -1) {
						install_area = a_id;
						apparatus_status[app_id].window = j;
						apparatus_status[app_id].area = install_area;
					}
				}
			}
		}
	}
}

int main() {
	read_window_info();
	read_apparatus();
	//test();
	install_bfs();
	//test();
	re_install();
	output();
}

