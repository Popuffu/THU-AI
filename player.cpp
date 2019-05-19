#include "api.h"
#include "base.h"
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <cmath>
#include <queue>
#include <set>
#define it1 multiset < Node*, QueueCompare >::iterator
using namespace ts20;
using namespace std;
struct Thing;
struct ChangedItem;

const double pi = 3.14159265358979;
const double boundMax = 35.0, boundMin = 7.0;//Ѱ·��Զ���루����ʱ��
const double collectLimit = 37.0;//ѡ��Ҫ��������Զ����
const double predictEnemyPace = 0.2;//Ԥ�������һ�����ȱ���
const double poisonRatio[VOCATION_SZ][3][3] = {//ְҵ,ʱ���,�ڼ������������ڿ����ܶ�
{ {0.70, 0.30, 1.00}, {0.15, 0.85, 0.75}, {0.00, 0.95, 0.60} },  //medic
{ {0.65, 0.35, 0.95}, {0.10, 0.90, 0.70}, {0.00, 0.90, 0.55} },  //signalman
{ {0.60, 0.40, 0.90}, {0.05, 0.95, 0.65}, {0.00, 0.85, 0.50} },  //hack
{ {0.50, 0.50, 0.82}, {0.00, 0.98, 0.57}, {0.00, 0.80, 0.42} } };//sniper
const int valueEarlier[ITEM_SZ][VOCATION_SZ] = {//ǰ����Ʒ��ֵ���Ӵ�ǹ���أ�
	//	MEDIC    SIGALMAN	  HACK	   SNIPER			 NAME				   NUM
		{0,         0,         0,        0 },			//FIST					0
		{5,         5,		   5,		 5 },			//HAND_GUN				1
		{25,		25,		   25,		 25},			//SUBMACHINE_GUN		2
		{10,	    10,		   10,		 10},			//SEMI_AUTOMATIC_RILE	3
		{16,		16,		   16,		 16},			//ASSAULT_RIFLE			4
		{60,		60,		   60,		 60},			//MACHINE_GUN			5
		{10,		10,		   10,		 14},			//SNIPER_RILFE			6
		{10,		10,		   10,		 14},			//SNIPER_BARRETT		7
		{0,			0,		   0,		 0 },			//TIGER_BILLOW_HAMMER	8
		{6,		    6,		   6,		 6 },			//CROSSBOW				9

		{5,			5,		   5,		 5 },			//VEST_1				10
		{10,		10,		   10,		 10},			//VEST_2				11
		{15,		15,		   15,		 15},			//VEST_3				12
		{8,			8,		   8,		 8 },			//INSULATED_CLOTHING	13

		{10,		10,		   10,		 10},			//MUFFLER				14
		{6,		    6,		   6,		 6 },			//BONDAGE				15
		{25,		25,		   25,		 25},			//FIRST_AID_CASE		16
		{0,         0,         9,        0 },			//CODE_CASE				17
		{0,         0,         0,        0 },			//SCOPE_2				18
		{0,         0,         0,        0 },			//SCOPE_4				19
		{0,         0,         0,        0 } };			//SCOPE_8				20
const int valueLater[ITEM_SZ][VOCATION_SZ] = {//������Ʒ��ֵ
	//	MEDIC    SIGALMAN	  HACK	   SNIPER			  NAME				   NUM
		{0,         0,         0,        0 },			//FIST					0
		{0,         0,		   0,		 0 },			//HAND_GUN				1
		{10,		10,		   10,		 10},			//SUBMACHINE_GUN		2
		{8,		    8,		   8,		 8 },			//SEMI_AUTOMATIC_RILE	3
		{15,		15,		   15,		 15},			//ASSAULT_RIFLE			4
		{30,		30,		   30,		 30},			//MACHINE_GUN			5
		{6,			6,		   6,		 12},			//SNIPER_RILFE			6
		{6,			6,		   6,		 12},			//SNIPER_BARRETT		7
		{0,			0,		   0,		 0 },			//TIGER_BILLOW_HAMMER	8
		{0,		    0,		   0,		 0 },			//CROSSBOW				9

		{5,			5,		   5,		 5 },			//VEST_1				10
		{10,		10,		   10,		 10},			//VEST_2				11
		{15,		15,		   15,		 15},			//VEST_3				12
		{8,			8,		   8,		 8 },			//INSULATED_CLOTHING	13

		{10,		10,		   10,		 10},			//MUFFLER				14
		{6,		    6,		   6,		 6 },			//BONDAGE				15
		{25,		25,		   25,		 25},			//FIRST_AID_CASE		16
		{0,         0,         9,        0 },			//CODE_CASE				17
		{0,         0,         0,        0 },			//SCOPE_2				18
		{0,         0,         0,        0 },			//SCOPE_4				19
		{0,         0,         0,        0 } };			//SCOPE_8				20

extern XYPosition start_pos, over_pos;//���ߵ�������յ��XY����
extern std::vector <int> teammates;//����ID
extern int frame;//��ǰ֡������0��ʼ������
extern PlayerInfo info;//������Ϣ�ľۺ�
vector <ChangedItem> change;//��¼����������Ʒ����ֹ��
vector <XYPosition> path, itemPath;//�ֱ��¼��Ҫ�ߵ�·�͵���Ŀ����Ʒ��·�����ڼ���ʵ�ʾ��룩
priority_queue <Thing, vector<Thing>> todo, todoPrint;//�洢ÿ�غ�Ҫ�ɵ����飬print�������
enum STATUS nowStatus;//��ǰ״̬������info.self.status��
XYPosition destination, shrink, pace, enemyPace, myPace, grassPos;
int landform[1000][1000], landformValue[1000][1000];//�ֱ��¼���κ͵��ε�����
int wCost[1000][1000], whCost[1000][1000];//�ֱ��¼�����б���ƶ�����
int demand[6];//0��������1���ף�2����������3��ҩƷ��4�������䣬5������Ͱ��ȭͷ�����δ�����Զ���Ȳ�Ҫ�Ķ�����
int durability[ITEM_SZ];//��ǰ������Ʒdurability
int delay;//ÿ�غϼ����ʱ
int follow;//�Ƿ�����Ʒ
int inside;//0��curOut��nextOut��1��curIn��nextOut��2��curIn��nextIn
int seeEnemy, collectGarbage;//����������ֵ
int totalHurt, totalHeal;//��ǰ������������ɵ����˺��͵�ǰ����ҩƷ���ܻ�Ѫ��
double nowViewAng;//��ǰ�ӽǣ�����info.self.view_angle����
double idealMove, idealView;//����Moveָ��ʱ���ƶ��ǶȺ��ӽ�

int LimitBound(int x)
{
	if (x < 0)
		return 0;
	else if (x > 999)
		return 999;
	else
		return x;
}
double LimitBound(double x)
{
	if (x < 0.0)
		return 0.0;
	else if (x > 999.0)
		return 999.0;
	else
		return x;
}
template<class T>
T Max(T a, T b)
{
	return a > b ? a : b;
}
template<class T>
T Min(T a, T b)
{
	return a < b ? a : b;
}
double AngleLimit(double a)//0-360
{
	while (a < 0.0)
		a += 360.0;
	while (a > 360.0)
		a -= 360.0;
	return a;
}
int DoubleToInt(double a)
{
	if (a > 0)
		return (int)((a * 2 + 1) / 2);
	else
		return (int)((a * 2 - 1) / 2);
}
bool DoubleEqual(double a, double b, double limit = 1e-3)
{
	if (fabs(a - b) < limit)
		return true;
	else
		return false;
}
PolarPosition XYToPolar(XYPosition finish)//ע�����ӽ��й�
{
	PolarPosition a;
	a.distance = sqrt((finish.x - info.self.xy_pos.x)*(finish.x - info.self.xy_pos.x) + (finish.y - info.self.xy_pos.y)*(finish.y - info.self.xy_pos.y));
	a.angle = AngleLimit(180.0 * atan2(finish.y - info.self.xy_pos.y, finish.x - info.self.xy_pos.x) / pi - nowViewAng);
	return a;
}
XYPosition PolarToXY(PolarPosition p, bool nowAng = true)//ע�����ӽ��й�
{
	XYPosition a;
	double ang = nowViewAng;
	if (nowAng != true)
		ang = info.self.view_angle;
	a.x = LimitBound(info.self.xy_pos.x + p.distance * cos(((p.angle + ang) / 180.0) * pi));
	a.y = LimitBound(info.self.xy_pos.y + p.distance * sin(((p.angle + ang) / 180.0) * pi));
	return a;
}
enum ToDoType//Ҫ�����������ֵ࣬��Ϊ�����ȼ�
{
	SHOOT = 6,
	HEAL = 5,
	RUN = 4,
	COLLECT = 3,
	CHASE_ENEMY = 2,
	CHASE_ITEM = 1,
	WANDER = 0,
	SZ = 7
};
struct ChangedItem
{
	XYPosition pos;
	ITEM type;
	ChangedItem(XYPosition p, ITEM i)
	{
		this->pos = p;
		this->type = i;
	}
};
struct Thing//Ҫ��������
{
	ToDoType type;
	XYPosition destination;
	ITEM item;
	int id;
	int mode;//only for CHASE_ENEMY
	double ang;
	int priority;//���ڱȽ����ȼ�
	Thing()
	{
		this->type = WANDER;
		this->destination = XYPosition{ 0,0 };
		this->id = 0;
		this->mode = 0;
		this->ang = 0.0;
		this->item = FIST;
		this->priority = 0;
	}
	Thing(ToDoType t, XYPosition d)//for Move(RUN, CHASE, WANDER)
	{
		this->type = t;
		this->destination = d;
		this->id = 0;
		this->mode = 0;
		this->ang = 0.0;
		this->item = FIST;
		this->priority = 10 * (int)t;
	}
	Thing(ToDoType t, XYPosition d, int i)//for Move(RUN, CHASE, WANDER)
	{
		this->type = t;
		this->destination = d;
		this->id = i;
		this->mode = 0;
		this->ang = 0.0;
		this->item = FIST;
		this->priority = 10 * (int)t;
	}
	Thing(ToDoType t, XYPosition d, ITEM it)//for Move(RUN, CHASE, WANDER)
	{
		this->type = t;
		this->destination = d;
		this->id = 0;
		this->mode = 0;
		this->ang = 0.0;
		this->item = it;
		this->priority = 10 * (int)t;
	}
	Thing(ToDoType t, int i, ITEM it)//for Collect
	{
		this->type = t;
		this->destination = XYPosition{ 0.0,0.0 };
		this->id = i;
		this->mode = 0;
		this->ang = 0.0;
		this->item = it;
		this->priority = 10 * (int)t;
	}
	Thing(ToDoType t, XYPosition d, ITEM i, double a, int idt = 0, int p = 0)//for Heal & Shoot
	{
		this->type = t;
		this->destination = d;
		this->id = idt;
		this->mode = 0;
		this->ang = a;
		this->item = i;
		this->priority = 10 * (int)t + p;
	}
}sucTodo1, sucTodo2, realShoot;//ÿ�غϳɹ����������£�realShoot�洢Ҫ������˵�λ�úͽǶ�
bool operator < (Thing a, Thing b)
{
	return ((a.priority < b.priority) || (a.priority == b.priority && a.type < b.type));
}
bool operator == (Thing a, Thing b)
{
	return  (a.ang == b.ang && a.id == b.id && a.item == b.item && a.priority == b.priority && a.type == b.type && a.destination.x == b.destination.x && a.destination.y == b.destination.y);
}
struct Node//Ѱ·���
{
	int x, y;//����
	int g; //��ʼ�㵽��ǰ��ʵ�ʴ���
	int h;//��ǰ�ڵ㵽Ŀ��ڵ����·���Ĺ��ƴ���
	int f;//����ֵ
	Node* father;
	Node()
	{
		this->x = 0;
		this->y = 0;
		this->g = 0;
		this->h = 0;
		this->f = 0;
		this->father = NULL;
	}
	Node(XYPosition p)
	{
		this->x = LimitBound((int)p.x);
		this->y = LimitBound((int)p.y);
		this->g = 0;
		this->h = 0;
		this->f = 0;
		this->father = NULL;
	}
	Node(int x, int y)
	{
		this->x = LimitBound(x);
		this->y = LimitBound(y);
		this->g = 0;
		this->h = 0;
		this->f = 0;
		this->father = NULL;
	}
	Node(int x, int y, Node* father)
	{
		this->x = LimitBound(x);
		this->y = LimitBound(y);
		this->g = 0;
		this->h = 0;
		this->f = 0;
		this->father = father;
	}
};
struct QueueCompare
{
	bool operator () (const Node *n1, const Node *n2) const
	{
		return (n1->f < n2->f) || ((n1->f == n2->f) && (n1->y < n2->y)) || ((n1->f == n2->f) && (n1->y == n2->y) && (n1->x < n2->x));
	}
};
struct XYInt//int���͵�XYPosition
{
	int x, y;
	XYInt() { x = 0, y = 0; }
	XYInt(XYPosition a)
	{
		x = DoubleToInt(a.x);
		y = DoubleToInt(a.y);
	}
	XYInt(int xi, int yi)
	{
		x = xi, y = yi;
	}
};
double Dist(XYPosition start, XYPosition finish)
{
	return sqrt((finish.x - start.x) * (finish.x - start.x) + (finish.y - start.y) * (finish.y - start.y));
}
double Dist(Node start, Node finish)
{
	return sqrt((finish.x - start.x) * (finish.x - start.x) + (finish.y - start.y) * (finish.y - start.y));
}
int UnitValue(ITEM t)//���ص�ǰ״̬��t������Ʒ��value
{
	if (totalHurt <= 150 && t >= 1 && t <= 9 && t != 8)//ûǹ
		return 1000;
	if (totalHeal <= 40 && t >= 15 && t <= 16)//ûҩ
		return valueLater[t][info.self.vocation] * 2;
	if (totalHurt < 800)
		return valueEarlier[t][info.self.vocation];
	else
		return valueLater[t][info.self.vocation];
}
int InPoison(XYPosition d)//�ж������ڶ�Ȧ��λ��
{
	int in = 0, time = 0;
	if (frame <= 200 || frame >= 2830)//��û��Ȧ����û��
		return 2;
	if (frame <= 600)
		time = 0;
	else if (frame <= 1340)
		time = 1;
	else
		time = 2;
	if (Dist(d, info.poison.current_center) <= info.poison.current_radius * poisonRatio[info.self.vocation][time][0] + info.poison.next_radius * poisonRatio[info.self.vocation][time][1])
		in++;
	if (Dist(d, info.poison.next_center) <= info.poison.next_radius * poisonRatio[info.self.vocation][time][2])
		in++;
	return in;
}
class BFS//����������������ڸ�����Ŀ�������Ŀɵ���ĵ�����
{
public:
	BFS()
	{
		memset(contain, 0, sizeof(contain));
	}
	XYPosition SearchAccess(XYPosition s)//Ѱ���ܵ���ĵ�
	{
		org.x = DoubleToInt(s.x), org.y = DoubleToInt(s.y);
		dorg = s;
		XYInt tmp;
		XYPosition a = s;
		if (s.x > 999 || s.x < 0 || s.y > 999 || s.y < 0 || org.x < 0 || org.x > 999 || org.y < 0 || org.y > 999)//�����յ����	
		{
			a.x = LimitBound(s.x);
			a.y = LimitBound(s.y);
			return a;
		}
		if (landform[org.x][org.y] <= 2)//�յ�������
			return a;
		memset(contain, 0, sizeof(contain));
		while (!visit.empty())
			visit.pop();
		visit.push(org);
		contain[org.x][org.y] = 1;
		while (visit.size() > 0)
		{
			tmp = visit.front();
			if (landform[tmp.x][tmp.y] <= 2)
			{
				a.x = (double)tmp.x, a.y = (double)tmp.y;
				return a;
			}
			visit.pop();
			AddPoint(tmp.x - 1, tmp.y);
			AddPoint(tmp.x + 1, tmp.y);
			AddPoint(tmp.x, tmp.y - 1);
			AddPoint(tmp.x, tmp.y + 1);
		}
		return a;
	}
private:
	void AddPoint(int x, int y)
	{
		XYPosition tmp;
		tmp.x = x, tmp.y = y;
		if (contain[x][y] == 1 || x < 0 || x >= 1000 || y < 0 || y >= 1000 || Dist(dorg, tmp) > 80.0)//����Ǵ󺣣�50����2=71	
			return;
		else
		{
			visit.push(XYInt(x, y));
			contain[x][y] = 1;
		}
	}
	bool contain[1000][1000];
	XYInt org;
	XYPosition dorg;
	queue <XYInt> visit;
}finder;
class Astar//����Ѱ· 
{
public:
	bool Search(Node* startPos, Node* endPos, bool isItem);
	double RealDist(XYPosition d);
private:
	void CheckPoint(int x, int y, it1 father, bool side);
	void NextStep(it1 currentPoint);
	void CountGHF(Node* sNode, Node* eNode, int g);
	bool UnWalk(int x, int y);
	void RecordPath(Node* current);
	void RecordItemPath(Node* current);
	multiset < Node*, QueueCompare > openList;
	Node *start;
	Node *end;
	bool openContain[1000][1000];//��ϣ���ж��Ƿ������õ�
	bool closeContain[1000][1000];//��ϣ���ж��Ƿ������õ�
	Node dustbin[1000 * 1000];//���ڴ洢�Ѿ��ӽ�ȥ�ĵ�
	int db_count;
	it1 it[1000][1000];
}astar;
bool Astar::Search(Node* startPos, Node* endPos, bool isItem = false)//�п��ܿ�ʼ�ĵط��ǲ����ߵģ���ǽ���ˣ����Ż�
{
	if (startPos->x < 0 || startPos->x >= 1000 || startPos->y < 0 || startPos->y >= 1000 || endPos->x < 0 || endPos->x >= 1000 || endPos->y < 0 || endPos->y >= 1000)
		return 0;
	if (landform[endPos->x][endPos->y] > 2 || landform[startPos->x][startPos->y] > 2)
		return 0;
	memset(openContain, 0, sizeof(openContain));
	memset(closeContain, 0, sizeof(closeContain));
	openList.clear();
	path.clear();
	itemPath.clear();
	it1 current;
	db_count = 0;
	this->start = startPos;
	this->end = endPos;
	it[startPos->x][startPos->y] = openList.insert(startPos);
	openContain[startPos->x][startPos->y] = 1;
	//��Ҫ����飬�ѿ�ʼ�Ľڵ����openlist��ʼ�����Աߵ�8���ڵ㣬������곬����Χ����closelist��return ����Ѿ�����openlist�ͶԱȵ�ǰ�ڵ㵽���������Ǹ��ڵ��Gֵ�͵�ǰ�ڵ㵽ԭ�����ڵ��Gֵ ���ԭ����Gֵ�Ƚϴ� ���ù� �������¸�ֵGֵ ���ڵ� ��f ������½ڵ� ���뵽openlist ֱ��opellistΪ�ջ��ҵ��յ�
	while (openList.size() > 0)
	{
		current = openList.begin();
		if ((*current)->x == endPos->x && (*current)->y == endPos->y)
		{
			if (isItem)//�ݹ��¼·��
				RecordItemPath(*current);
			else
				RecordPath(*current);
			return 1;
		}
		NextStep(current);
		closeContain[(*current)->x][(*current)->y] = 1;
		openContain[(*current)->x][(*current)->y] = 0;
		openList.erase(current);
	}
	return 0;
}
void Astar::CheckPoint(int x, int y, it1 father, bool side)//side=1��б���ߣ�side=0��ˮƽ��ֱ��
{
	if (x < 0 || x >= 1000 || y < 0 || y >= 1000)
		return;
	if (this->UnWalk(x, y))
		return;
	if (closeContain[x][y] == 1)
		return;
	int gin;//����б������
	if (side)
		gin = whCost[x][y];
	else
		gin = wCost[x][y];
	if (openContain[x][y] == 1)
	{
		Node* point = *it[x][y];
		if (point->g > (*father)->g + gin)
		{
			openList.erase(it[x][y]);
			point->father = *father;
			point->g = (*father)->g + gin;
			point->f = point->g + point->h;
			it[x][y] = openList.insert(point);
		}
	}
	else
	{
		Node *point = &(dustbin[++db_count] = Node(x, y, *father));
		CountGHF(point, end, gin);
		it[point->x][point->y] = openList.insert(point);
		openContain[point->x][point->y] = 1;
	}
}
void Astar::NextStep(const it1 current)//�˷���Ѱ·
{
	CheckPoint((*current)->x - 1, (*current)->y, (current), 0);//��
	CheckPoint((*current)->x + 1, (*current)->y, (current), 0);//��
	CheckPoint((*current)->x, (*current)->y + 1, (current), 0);//��
	CheckPoint((*current)->x, (*current)->y - 1, (current), 0);//��
	CheckPoint((*current)->x - 1, (*current)->y + 1, (current), 1);//����
	CheckPoint((*current)->x - 1, (*current)->y - 1, (current), 1);//����
	CheckPoint((*current)->x + 1, (*current)->y - 1, (current), 1);//����
	CheckPoint((*current)->x + 1, (*current)->y + 1, (current), 1);//����
}
void Astar::CountGHF(Node* sNode, Node* eNode, int g)
{
	int h = abs(sNode->x - eNode->x) + abs(sNode->y - eNode->y) * 10;//ֱ������
	int currentg = sNode->father->g + g;
	int f = currentg + h;
	sNode->f = f;
	sNode->h = h;
	sNode->g = currentg;
}
bool Astar::UnWalk(int x, int y)
{
	if (landform[x][y] > 2)
		return true;
	return false;
}
void Astar::RecordPath(Node* current)
{
	if ((current)->father != NULL)
	{
		XYPosition p;
		RecordPath((current)->father);
		p.x = (double)((current)->x) + 0.5, p.y = (double)((current)->y) + 0.5;
		path.push_back(p);
	}
}
void Astar::RecordItemPath(Node* current)
{
	if ((current)->father != NULL)
	{
		XYPosition p;
		RecordItemPath((current)->father);
		p.x = (double)((current)->x) + 0.5, p.y = (double)((current)->y) + 0.5;
		itemPath.push_back(p);
	}
}
double Astar::RealDist(XYPosition d)//������Ŀ����ʵ�ʾ��룬������·����Ȧ���򷵻ؾ��룬���򷵻ؾ��븺ֵ
{
	Node start(d), end(info.self.xy_pos);
	Node *pNodea = &start, *pNodeb = &end;
	Search(pNodeb, pNodea, true);
	if (itemPath.size() < 5)
	{
		double l = Dist(d, info.self.xy_pos);
		if (frame <= 200 || frame >= 2830)
			return l;
		for (int i = 0; i < itemPath.size(); i++)
			if (InPoison(itemPath[i]) != 2)
				return -l;
		return l;
	}
	int f = 2, b = itemPath.size() - 3;//front, back
	double rd = Dist(info.self.xy_pos, itemPath[f]) + Dist(d, itemPath[b]);//realDist
	while (true)
	{
		if (b - f < 3)
			break;
		rd += Dist(itemPath[f], itemPath[f + 3]);
		f += 3;
		if (b - f < 3)
			break;
		rd += Dist(itemPath[b], itemPath[b - 3]);
		b -= 3;
	}
	rd += Dist(itemPath[f], itemPath[b]);
	if (frame <= 200 || frame >= 2830)
		return rd;
	for (int i = 0; i < itemPath.size(); i++)
		if (InPoison(itemPath[i]) != 2)
			return -rd;
	return rd;

}
bool IsFriend(int id)//�ж��Ƿ�Ϊ����
{
	for (int i = 0; i < teammates.size(); i++)
		if (id == teammates[i])
			return true;
	return false;
}
bool HaveItem(ITEM a)//�ж��Ƿ��и���Ʒ
{
	for (int i = 0; i < info.self.bag.size(); i++)
		if (info.self.bag[i].type == a && info.self.bag[i].durability > 0)
			return 1;
	return 0;
}
int HaveWeapon(double searchDist = 3.0)//searchdist=3����fist�ͻ��δ��������ܴ��е��˺���ߵ�ǹ֧��ţ�����ǹ֧�ͻ��δ�����û��ǹ����-1
{
	int num = -1, num2 = -1;
	double valueMax = 0, valueMax2 = 0;
	for (int i = 0; i <= 9; i++)
		if (searchDist <= ITEM_DATA[i].range && HaveItem((ITEM)i) && valueMax <= UnitValue((ITEM)i))
		{
			num = i;
			valueMax = UnitValue((ITEM)i);
		}
	if (num >= 6 && num <= 7 && searchDist <= 100.0)//���Ҿ���Ͻ���������û������ǹ
	{
		for (int i = 0; i <= 9; i++)
			if (i != 6 && i != 7 && searchDist <= ITEM_DATA[i].range && HaveItem((ITEM)i) && valueMax2 <= UnitValue((ITEM)i))
			{
				num2 = i;
				valueMax2 = UnitValue((ITEM)i);
			}
		if (num2 >= 0)
			return num2;
	}
	return Max(-1, num);
}
void Rect(BLOCK_TYPE t, int x1, int y1, int x2, int y2)//���ε���
{
	int xmin = LimitBound(Min(x1, x2));
	int xmax = LimitBound(Max(x1, x2));
	int ymin = LimitBound(Min(y1, y2));
	int ymax = LimitBound(Max(y1, y2));
	for (int j = ymin; j <= ymax; j++)
		for (int i = xmin; i <= xmax; i++)
			switch (t)
			{
			case SHALLOW_WATER://����ͨ�е������
				landform[i][j] = 2;
				landformValue[i][j] = 10;
				break;
			case RECTANGLE_GRASS:case CIRCLE_GRASS://����ͨ�п�������
				landform[i][j] = 1;
				landformValue[i][j] = 3;
				break;
			case DEEP_WATER://�޷�ͨ���޷����ӵ�������
				landform[i][j] = 6;
				landformValue[i][j] = 100;
				break;
			case WALL://�޷�ͨ���޷����ӵ�����С
				landform[i][j] = 5;
				landformValue[i][j] = 100;
				break;
			case RECTANGLE_BUILDING:case CIRCLE_BUILDING://�޷�ͨ���ܵ��ӵ�����һ�
				landform[i][j] = 4;
				landformValue[i][j] = 100;
				break;
			case TREE://�޷�ͨ���ܵ��ӵ���С�һ�
				landform[i][j] = 3;
				landformValue[i][j] = 100;
				break;
			default://����ͨ��
				break;
			}
}
void Circ(BLOCK_TYPE t, int x, int y, int r)//Բ�ε���
{
	XYPosition a, b;
	int xmin = LimitBound(x - r);
	int xmax = LimitBound(x + r);
	int ymin = LimitBound(y - r);
	int ymax = LimitBound(y + r);
	for (int j = ymin; j <= ymax; j++)
		for (int i = xmin; i <= xmax; i++)
		{
			a.x = i, a.y = j;
			b.x = x, b.y = y;
			if (Dist(a, b) <= (double)r + 1e-3)
			{
				switch (t)
				{
				case SHALLOW_WATER://����ͨ�е������
					landform[i][j] = 2;
					landformValue[i][j] = 10;
					break;
				case RECTANGLE_GRASS:case CIRCLE_GRASS://����ͨ�п�������
					landform[i][j] = 1;
					landformValue[i][j] = 3;
					break;
				case DEEP_WATER://�޷�ͨ���޷����ӵ�������
					landform[i][j] = 6;
					landformValue[i][j] = 100;
					break;
				case WALL://�޷�ͨ���޷����ӵ�����С
					landform[i][j] = 5;
					landformValue[i][j] = 100;
					break;
				case RECTANGLE_BUILDING:case CIRCLE_BUILDING://�޷�ͨ���ܵ��ӵ�����һ�
					landform[i][j] = 4;
					landformValue[i][j] = 100;
					break;
				case TREE://�޷�ͨ���ܵ��ӵ���С�һ�
					landform[i][j] = 3;
					landformValue[i][j] = 100;
					break;
				default://����ͨ��
					break;
				}
			}
		}
}
void MapProcess()//��ʼ��landform��landformValue����
{
	memset(landform, 0, sizeof(landform));
	memset(wCost, 0, sizeof(wCost));
	memset(whCost, 0, sizeof(whCost));
	for (int i = 0; i < 1000; i++)
		for (int j = 0; j < 1000; j++)
			landformValue[i][j] = 5;
	for (int y = 9; y >= 0; y--)
	{
		for (int x = 0; x < 10; x++)
		{
			AREA num = MAP[y * 10 + x];
			int offsetx = x * 100, offsety = y * 100;
			for (int i = 0; i < AREA_DATA[num].size(); i++)
			{
				if (AREA_DATA[num][i].shape == RECTANGLE)
					Rect(AREA_DATA[num][i].type, offsetx + AREA_DATA[num][i].x0, offsety + AREA_DATA[num][i].y0 - 1, offsetx + AREA_DATA[num][i].x1 - 1, offsety + AREA_DATA[num][i].y1);
				else if (AREA_DATA[num][i].shape == CIRCLE)
					Circ(AREA_DATA[num][i].type, offsetx + AREA_DATA[num][i].x0, offsety + AREA_DATA[num][i].y0, AREA_DATA[num][i].r);
			}
		}
	}
}
void CostProcess(int part)//���ڳ�ʼ��wCost��whCost����10���֣�����12345678910���Է���ʱ
{
	const int r = 3;
	static int count;
	int start, end;
	if (part < 1 || part > 10)
		return;
	else
	{
		start = (part - 1) * 100;
		end = part * 100;
	}
	for (int i = start; i < end; i++)
	{
		for (int j = 0; j < 1000; j++)
		{
			int xmin = LimitBound(i - r), xmax = LimitBound(i + r),
				ymin = LimitBound(j - r), ymax = LimitBound(j + r);
			int cnt = 0, sum = 0;
			for (int ii = xmin; ii <= xmax; ii++)
			{
				for (int jj = ymin; jj <= ymax; jj++)
				{
					if (abs(ii - i) + abs(jj - j) <= r)
					{
						cnt++;
						sum += landformValue[ii][jj];
					}
				}
			}
			sum = sum / cnt;
			wCost[i][j] = 5 * sum;
			whCost[i][j] = 7 * sum;
			count++;
		}
	}
}
bool RectIntersect(double ang, double x0, double y0, double x1, double y1, double critical)//�жϴ�ԭ����������Ϊang��ֱ���Ƿ���Ŀ������ཻ��angΪ���ԽǶȣ�����Ϊ�������ڴ�Ϊԭ���������
{
	XYPosition leftUp, rightUp, leftLow, rightLow;
	double a = AngleLimit(ang);
	int quadrant;//����
	if (x0 < 0.0 && y0 > 0.0 && x1 > 0.0 && y1 < 0.0)//�������Χ	
		return true;
	if (a >= 0.0 && a < 90.0)
		quadrant = 1;
	else if (a >= 90.0 && a < 180.0)
		quadrant = 2;
	else if (a >= 180.0 && a < 270.0)
		quadrant = 3;
	else
		quadrant = 4;
	switch (quadrant)
	{
	case 1:
		leftUp.x = x0, leftUp.y = y0;
		rightLow.x = x1, rightLow.y = y1;
		break;
	case 2:
		a -= 90.0;
		leftUp.x = y1, leftUp.y = -x0;
		rightLow.x = y0, rightLow.y = -x1;
		break;
	case 3:
		a -= 180.0;
		leftUp.x = -x1, leftUp.y = -y1;
		rightLow.x = -x0, rightLow.y = -y0;
		break;
	default://case 4:
		a -= 270.0;
		leftUp.x = -y0, leftUp.y = x1;
		rightLow.x = -y1, rightLow.y = x0;
		break;
	}//ȫ��ת����һ���ޣ���ʱ0 <= a < 90
	rightUp.x = rightLow.x, rightUp.y = leftUp.y;
	leftLow.x = leftUp.x, leftLow.y = rightLow.y;
	double s = sin(a * pi / 180.0), c = cos(a * pi / 180.0);
	if (s * rightLow.x < c * rightLow.y || s * leftUp.x > c * leftUp.y)//�޽���
		return false;
	if (DoubleEqual(a, 90.0))
	{
		if (leftUp.x > 0.0 || rightLow.x < 0.0)
			return false;
		else if (rightLow.y >= 0 && rightLow.y <= critical)
			return true;
		else
			return false;
	}
	else if (DoubleEqual(a, 0.0))
	{
		if (leftUp.y < 0.0 || rightLow.y > 0.0)
			return false;
		else if (leftUp.x >= 0 && leftUp.x <= critical)
			return true;
		else
			return false;
	}
	XYPosition org, point;
	org.x = org.y = 0.0;
	double l;//�������
	if (s * leftLow.x > c * leftLow.y)//���������½�֮��
	{
		if (s * rightUp.x > c * rightUp.y)//���������½�֮�ϣ����Ͻ�֮�ϣ�����λ����߻��ϱ�
		{
			if (leftUp.x >= 0.0)
				point.x = leftUp.x, point.y = point.x * tan(a * pi / 180.0);
			else
				point.y = leftUp.y, point.x = point.y / tan(a * pi / 180.0);
			if (point.y < 0)
				return false;
		}
		else//���������½�֮�ϣ����Ͻ�֮�£�����λ����߻��ұ�
		{
			if (leftUp.x >= 0.0)
				point.x = leftUp.x, point.y = point.x * tan(a * pi / 180.0);
			else
				point.x = rightLow.x, point.y = point.x * tan(a * pi / 180.0);
			if (point.x < 0)
				return false;
		}
	}
	else
	{
		if (s * rightUp.x > c * rightUp.y)//���������½�֮�£����Ͻ�֮�ϣ�����λ���ϱ߻��±�
		{
			if (rightLow.y >= 0.0)
				point.y = rightLow.y, point.x = point.y / tan(a * pi / 180.0);
			else
				point.y = leftUp.y, point.x = point.y / tan(a * pi / 180.0);
			if (point.y < 0)
				return false;
		}
		else//���������½�֮�£����Ͻ�֮�£�����λ���±߻��ұ�
		{
			if (rightLow.y >= 0.0)
				point.y = rightLow.y, point.x = point.y / tan(a * pi / 180.0);
			else
				point.x = rightLow.x, point.y = point.x * tan(a * pi / 180.0);
			if (point.x < 0)
				return false;
		}
	}
	l = Dist(org, point);
	if (l >= 0.0 && l <= critical)
		return true;
	else
		return false;
}
bool CircIntersect(double ang, double x0, double y0, double r, double critical)//�жϴ�ԭ����������Ϊang��ֱ���Ƿ���Ŀ��Բ���ཻ��angΪ���ԽǶȣ�����Ϊ�������ڴ�Ϊԭ���������
{
	double a = AngleLimit(ang), s = sin(a * pi / 180.0), c = cos(a * pi / 180.0);
	double delta = r * r - (c * y0 - s * x0) * (c * y0 - s * x0);//�б�ʽ
	if ((r * r - y0 * y0 - x0 * x0) >= 0)//����Բ��
		return true;
	if (delta < 0.0)//�޽���
		return false;
	delta = sqrt(delta);
	double l = (c * x0 + s * y0 - delta);
	if (l >= 0.0 && l <= critical)
		return true;
	else
		return false;
}
bool Intersect(XYPosition og, double ang, double bias, double critical = 0.6)//�жϴ�ԭ����������Ϊang��ֱ���Ƿ���ĳ���е����ཻ
{
	XYPosition tmp;
	tmp.x = tmp.y = 50.0;
	for (int y = 9; y >= 0; y--)
	{
		for (int x = 0; x < 10; x++)
		{
			AREA num = MAP[y * 10 + x];
			double offsetx = (double)(x * 100) - og.x, offsety = (double)(y * 100) - og.y;
			if (Dist(tmp, XYPosition{ (double)offsetx, (double)offsety }) > 220.0)//�Դ���150����2
				continue;
			for (int i = 0; i < AREA_DATA[num].size(); i++)
			{
				if (AREA_DATA[num][i].shape == RECTANGLE && AREA_DATA[num][i].type != SHALLOW_WATER && AREA_DATA[num][i].type != RECTANGLE_GRASS && AREA_DATA[num][i].type != CIRCLE_GRASS)
				{
					if (RectIntersect(ang, offsetx + AREA_DATA[num][i].x0 - bias, offsety + AREA_DATA[num][i].y0 + bias, offsetx + AREA_DATA[num][i].x1 + bias, offsety + AREA_DATA[num][i].y1 - bias, critical))
						return true;
				}
				else if (AREA_DATA[num][i].shape == CIRCLE && AREA_DATA[num][i].type != SHALLOW_WATER && AREA_DATA[num][i].type != RECTANGLE_GRASS && AREA_DATA[num][i].type != CIRCLE_GRASS)
				{
					if (CircIntersect(ang, offsetx + AREA_DATA[num][i].x0, offsety + AREA_DATA[num][i].y0, AREA_DATA[num][i].r + bias, critical))
						return true;
				}
			}
		}
	}
	return false;
}
void Initial(VOCATION profession)//��Ϣ���¡���ɡ����ʼ��������
{
	static int initialPart = 0, iii = 0;
	update_info();
	if (frame == 0)
	{
		XYPosition jump;
		switch (profession)//ѡ����ɡ�ص�
		{
		case MEDIC:
			jump.x = 433, jump.y = 415;//���ĳ����½�
			break;
		case SNIPER:
			jump.x = 450, jump.y = 315;//ɽ������
			break;
		case HACK:
			jump.x = 163.5, jump.y = 181;//���³����Ͻ�
			break;
		default://signalman
			jump.x = 135, jump.y = 181;//���³����Ͻ�
			break;
		}
		parachute(profession, jump);
		MapProcess();
	}
	else
	{
		if (initialPart < 10)
			CostProcess(++initialPart);
		srand((unsigned int)(time(nullptr) + info.player_ID * frame));
		sucTodo1 = Thing();
		sucTodo2 = Thing();
		realShoot = Thing();
		nowViewAng = info.self.view_angle;
		nowStatus = info.self.status;
		grassPos.x = grassPos.y = 0.0;
		shrink.x = shrink.y = 0.0;
		pace.x = pace.y = 0.0;
		enemyPace.x = enemyPace.y = 0.0;
		myPace.x = myPace.y = 0.0;
		idealMove = idealView = 0.0;
	}
}
bool Shoot(ITEM item_type, double shoot_angle, int parameter = -1)//������ʹ�õĵ���/ǹ��ö�٣���ԽǶȣ����������ҽ�Ʊ�ʹ��ҩƷ�Ķ���ID���������Ƿ�ִ�гɹ�
{
	switch (nowStatus)
	{
	case RELAX:
		if (info.self.attack_cd > 0)
			return false;
		else
		{
			shoot(item_type, shoot_angle, parameter);
			nowStatus = SHOOTING;
			return true;
		}
	case MOVING:
		if (info.self.attack_cd > 0)
			return false;
		else
		{
			shoot(item_type, shoot_angle, parameter);
			nowStatus = MOVING_SHOOTING;
			return true;
		}
	default:
		return false;
	}
}
XYPosition MyPace(double moveAng, double length)//����Ԥ���Լ���һ��λ�ã�moveAngΪ���ԽǶȣ��ռ��궫����RELAX״̬���ܻ�Ԥ�����
{
	double l = VOCATION_DATA[info.self.vocation].move * length;
	if (collectGarbage == 2)
	{
		if (info.self.move_cd != 2)
			return XYPosition{ 0.0, 0.0 };
		l = VOCATION_DATA[info.self.vocation].move * 0.5;
	}
	for (int y = 9; y >= 0; y--)
	{
		for (int x = 0; x < 10; x++)
		{
			AREA num = MAP[y * 10 + x];
			int offsetx = x * 100, offsety = y * 100;
			if (num != POOL && num != FARMLAND)
				continue;
			for (int i = 0; i < AREA_DATA[num].size(); i++)
			{
				if (AREA_DATA[num][i].type == SHALLOW_WATER && info.self.xy_pos.x >= (double)(AREA_DATA[num][i].x0 + offsetx)
					&& info.self.xy_pos.x <= (double)(AREA_DATA[num][i].x1 + offsetx) && info.self.xy_pos.y <= (double)(AREA_DATA[num][i].y0 + offsety) && info.self.xy_pos.y >= (double)(AREA_DATA[num][i].y1 + offsety))//��ǳ̲�ڲ�
				{
					l *= 0.6;
					return XYPosition{ l * cos(moveAng * pi / 180.0), l * sin(moveAng * pi / 180.0) };
				}
			}
		}
	}
	return XYPosition{ l * cos(moveAng * pi / 180.0), l * sin(moveAng * pi / 180.0) };
}
bool Move(double move_angle, double view_angle, int strong = 0, int parameter = -1)//������ǰ���������ӽǵ���ԽǶȣ�����ڵ�ǰ�ӽǣ���parameter == NOMOVE(0)ʱ���ƶ���ֻ�����Ƕȣ������Ƿ�ִ�гɹ�
{
	if (parameter != NOMOVE)
	{
		switch (nowStatus)
		{
		case RELAX:case MOVING:
			nowStatus = MOVING;
			if (strong || info.self.move_cd != 2)
			{
				myPace = MyPace(AngleLimit(move_angle + nowViewAng), 0.2);
				move(move_angle, view_angle);
			}
			else
			{
				myPace = MyPace(info.self.move_angle, 0.5);
				move(0.0, view_angle, NOMOVE);
			}
			nowViewAng = AngleLimit(nowViewAng + view_angle);
			return true;
		case SHOOTING:case MOVING_SHOOTING:
			nowStatus = MOVING_SHOOTING;
			if (strong || info.self.move_cd != 2)
			{
				myPace = MyPace(AngleLimit(move_angle + nowViewAng), 0.2);
				move(move_angle, view_angle);
			}
			else
			{
				myPace = MyPace(info.self.move_angle, 0.5);
				move(0.0, view_angle, NOMOVE);
			}
			nowViewAng = AngleLimit(nowViewAng + view_angle);
			return true;
		default:
			return false;
		}
	}
	else
	{
		if (info.self.move_cd == 2)
			myPace = MyPace(AngleLimit(move_angle + nowViewAng), 0.5);
		else
			myPace = MyPace(AngleLimit(move_angle + nowViewAng), 0.2);
		move(move_angle, view_angle, NOMOVE);
		nowViewAng = AngleLimit(nowViewAng + view_angle);
		return true;
	}
}
bool Reachable(XYPosition p)//�ж��Ƿ��ܵ������Shrink����ʹ�ã��Ƚ���landform�ж�Ҫ�ϣ�������
{
	if (p.x < 0 || p.x > 999.0 || p.y < 0 || p.y > 999.0)
		return 0;
	return ((landform[(int)(p.x)][(int)(p.y)] <= 2) && wCost[(int)(p.x)][(int)(p.y)] <= 200);
}
Node Shrink(XYPosition des)//����һ��������ȷ������϶̵�Ŀ�������Ѱ·������Ѱ·�����Է���ʱ
{
	XYPosition close;
	PolarPosition polar;
	double delta;
	close.x = des.x, close.y = des.y;
	polar = XYToPolar(des);
	double absolute = AngleLimit(polar.angle + nowViewAng);//���ԽǶ�
	delta = 1 / Max(fabs(sin(absolute * pi / 180.0)), fabs(cos(absolute * pi / 180.0)));
	if (Reachable(des) && polar.distance < boundMax)//��������
		return Node(des);
	else if (polar.distance < boundMax)//����Ͻ���������
		return finder.SearchAccess(des);
	polar.distance = boundMax;
	while (polar.distance > boundMin)
	{
		polar.distance -= delta;
		close = PolarToXY(polar);
		if (Reachable(close))
			return Node(close);
	}
	polar.distance = boundMax;
	close = PolarToXY(polar);
	close = finder.SearchAccess(close);
	return Node(close);
}
bool Pickup(int target_ID, bool strong = false, int parameter = -1)//���������ϵ���ƷID����Ҫ��һ����Χ�ڲ��ܳɹ���PICKUP_DISTANCE������ΪstrongΪtrue���Ϲ���������ֻ����ƶ��������Ƿ�ִ�гɹ�
{
	switch (nowStatus)
	{
	case RELAX:case MOVING:
		pickup(target_ID, parameter);
		nowStatus = PICKUP;
		return true;
	case SHOOTING:case MOVING_SHOOTING:
		if (strong)
		{
			pickup(target_ID, parameter);
			nowStatus = PICKUP;
			return true;
		}
		return false;
	default:
		return false;
	}
}
bool Priority(ITEM a, ITEM b, double dista, double distb, int lock = 0)//�ж�a��b����Ʒ�ĸ����ã�b�÷���1��a�÷���0��lock = 1����Ʒ������
{
	int category[2];
	if (dista < 0 && distb > 0)
		return 1;
	if (distb < 0 && dista > 0)
		return 0;
	double da = fabs(dista), db = fabs(distb);
	switch (a)
	{
	case 1:case 2:case 3:case 4:case 5:case 6:case 7:case 9:
		category[0] = 0;
		break;
	case 10:case 11:case 12:case 13:
		category[0] = 1;
		break;
	case 14:
		category[0] = 2;
		break;
	case 15:case 16:
		category[0] = 3;
		break;
	case 17:
		category[0] = 4;
		break;
	default://0,8,18,19,20
		category[0] = 5;
		break;
	}
	switch (b)
	{
	case 1:case 2:case 3:case 4:case 5:case 6:case 7:case 9:
		category[1] = 0;
		break;
	case 10:case 11:case 12:case 13:
		category[1] = 1;
		break;
	case 14:
		category[1] = 2;
		break;
	case 15:case 16:
		category[1] = 3;
		break;
	case 17:
		category[1] = 4;
		break;
	default://0,8,18,19,20
		category[1] = 5;
		break;
	}
	if ((category[1] == 2 && demand[2] == 0) || (category[1] == 4 && demand[4] == 0) || category[1] == 5)
		return 0;
	double dist[2];
	dist[0] = Max(1.0, da - 3.0);
	dist[1] = Max(1.0, db - 3.0);
	if (demand[category[1]] == 0 && demand[category[0]] != 0)
		return 0;
	else if (demand[category[0]] == 0 && demand[category[1]] != 0)
		return 1;
	else
		return ((double)UnitValue(a) / dist[0] + lock * 1.0) < (double)UnitValue(b) / dist[1] ? 1 : 0;
}
int FindGarbageNum()//������õ���Ʒvector��ţ�û�з���-1
{
	if (info.items.size() < 1)
		return -1;
	int num = 0, flag = 0;
	for (int i = 0; i < info.items.size(); i++)
	{
		if (info.items[i].polar_pos.distance > collectLimit)
			continue;
		if ((i == 0 || Priority(info.items[num].type, info.items[i].type, astar.RealDist(PolarToXY(info.items[num].polar_pos)), astar.RealDist(PolarToXY(info.items[i].polar_pos)))) &&
			UnitValue(info.items[num].type) > 0 && InPoison(PolarToXY(info.items[i].polar_pos)) == 2)
		{
			num = i;
			flag = 1;
		}
	}
	return flag == 0 ? -1 : num;
}
bool CanSeeMe(int num)//������˱�ţ������Ƿ��ܿ����Լ���δ���Ǵ�ǽfeature��
{
	if (info.others[num].polar_pos.distance > VOCATION_DATA[info.others[num].vocation].distance)//̫Զ�˿�����
		return false;
	double abAng = AngleLimit(180.0 + nowViewAng + info.others[num].polar_pos.angle);//�����ӽǣ��Լ���Ե��˵ľ��ԽǶ�
	abAng = fabs(abAng - info.others[num].view_angle);
	if (abAng >= 180.0)
		abAng = 360.0 - abAng;//��λ�ú����߽ǶȲ��ǣ�
	return (abAng <= 0.5 * VOCATION_DATA[info.others[num].vocation].angle);
}
int FindEnemyNumRange(double lmin, double lmax, bool canSee)//Ѱ���ھ���Ϊlmin��lmax��Ѱ������ĵ��ˣ�canSee���Ƿ������ҿ����Լ��ģ�
{
	int num = -1;
	double minDist = 1000000.0;
	if (canSee)
	{
		for (int i = 0; i < info.others.size(); i++)
			if ((!IsFriend(info.others[i].player_ID)) && info.others[i].status != DEAD && info.others[i].status != REAL_DEAD && CanSeeMe(i) &&
				info.others[i].polar_pos.distance < lmax && info.others[i].polar_pos.distance > lmin && info.others[i].polar_pos.distance < minDist)
			{
				num = i;
				minDist = info.others[i].polar_pos.distance;
			}//�Ҿ��뷶Χ���ܿ����Լ�������ĵ���
		if (num >= 0)
			return num;
	}
	for (int i = 0; i < info.others.size(); i++)
		if ((!IsFriend(info.others[i].player_ID)) && info.others[i].status != DEAD && info.others[i].status != REAL_DEAD &&
			info.others[i].polar_pos.distance < lmax && info.others[i].polar_pos.distance > lmin && info.others[i].polar_pos.distance < minDist)
		{
			num = i;
			minDist = info.others[i].polar_pos.distance;
		}//�Ҿ��뷶Χ������ĵ���
	return Max(-1, num);
}
int FindEnemyNum()//Ѱ�ҵ��ˣ����ص��˱�ţ�û�з���-1
{
	double gunl = 0.0, maxDist = 0;//ӵ�е�ǹ�ܴ򵽵���Զ����
	for (int i = 0; i < info.self.bag.size(); i++)
		if (HaveItem(info.self.bag[i].type) && gunl < (double)(ITEM_DATA[info.self.bag[i].type].range))
			gunl = (double)(ITEM_DATA[info.self.bag[i].type].range);
	gunl = Min(VOCATION_DATA[info.self.vocation].distance, gunl);
	if (gunl < 10.0)//ֻ��ȭͷ���δ���ǹ֧�����������Ϊ80
		return FindEnemyNumRange(0.0, 5.0, false);//�Ҿ���Ϊ5֮������ĵ���
	int num = FindEnemyNumRange(10.0, 60.0, true);//�Ҿ���Ϊ10-60֮������ĵ��ˣ��������ܿ����Լ��ģ�
	if (num >= 0)
		return num;
	num = -1;
	for (int i = 0; i < info.others.size(); i++)
		if ((!IsFriend(info.others[i].player_ID)) && info.others[i].status != DEAD && info.others[i].status != REAL_DEAD &&
			info.others[i].polar_pos.distance < 10.0 && info.others[i].polar_pos.distance > 1.5 && info.others[i].polar_pos.distance > maxDist)
		{
			num = i;
			maxDist = info.others[i].polar_pos.distance;
		}//��10������Զ�ĵ���
	if (num >= 0)
		return num;
	num = FindEnemyNumRange(60.0, gunl + 20.0, true);//�Ҿ���Ϊ10-60֮������ĵ��ˣ��������ܿ����Լ��ģ�
	return num;
}
void RealShoot()//����
{
	if (realShoot.type == SHOOT)
	{
		XYPosition enemy = realShoot.destination;
		enemy.x += enemyPace.x - myPace.x;
		enemy.y += enemyPace.y - myPace.y;
		shoot(realShoot.item, XYToPolar(enemy).angle);
	}
}
bool DoFirstThing()//��todo���������ȼ���ߵ��Ǽ�����
{
	if (frame < 2 || info.self.status == ON_PLANE || info.self.status == JUMPING)
		return false;
	Thing f;
	XYPosition dest = destination;
	bool strong = 0;
	if (!todo.empty())
	{
		f = todo.top();//first thing to do
		dest = f.destination;
	}
	else
		f.type = WANDER;
	switch (f.type)
	{
	case SHOOT://��װ�Ѿ�������
		switch (nowStatus)
		{
		case RELAX:
			if (info.self.attack_cd > 0)
				return false;
			else
			{
				realShoot = f;
				nowStatus = SHOOTING;
				return true;
			}
		case MOVING:
			if (info.self.attack_cd > 0)
				return false;
			else
			{
				realShoot = f;
				nowStatus = MOVING_SHOOTING;
				return true;
			}
		default:
			return false;
		}
	case HEAL:
		return Shoot(f.item, f.ang);
	case COLLECT:
		return Pickup(f.id, true);
	case CHASE_ENEMY:
		follow = 0;
		if (f.mode > 1)//��Ϊ���Һ�������ǿ�ƶ�ָ��
			strong = 1;
		break;
	case RUN:
		follow = 1;
		break;
	case CHASE_ITEM:
		if (Dist(info.self.xy_pos, dest) < 6.0)
			follow = 0;
		else
			follow = 1;
		break;
	case WANDER:
		follow = 1;
		break;
	default://wander����������Ҫ��
		follow = 1;
		break;
	}
	if (follow < 0)
	{
		idealMove = 0.0;
		idealView = VOCATION_DATA[info.self.vocation].angle - 1.0;
		return Move(idealMove, idealView, NOMOVE, strong);
	}
	if (Dist(info.self.xy_pos, dest) < 3.0)
	{
		idealMove = idealView = XYToPolar(dest).angle;
		return Move(idealMove, idealView, strong);
	}
	Node a = Shrink(dest);
	shrink.x = a.x, shrink.y = a.y;
	Node b(info.self.xy_pos);
	Node *pNodea = &a, *pNodeb = &b;
	astar.Search(pNodeb, pNodea);
	if (!path.empty())
	{
		int xmin = LimitBound(DoubleToInt(info.self.xy_pos.x) - 2), xmax = LimitBound(DoubleToInt(info.self.xy_pos.x) + 2),
			ymin = LimitBound(DoubleToInt(info.self.xy_pos.y) - 2), ymax = LimitBound(DoubleToInt(info.self.xy_pos.y) + 2);
		int flag = 0;
		for (int i = xmin; i <= xmax; i++)
			for (int j = ymin; j <= ymax; j++)
				if (landform[i][j] > 2)
					flag++;
		XYPosition average;
		if (flag == 0)//��Χ���ϰ���
		{
			int sz = Min(6, (int)path.size());//ȡǰ6����ƽ��
			average.x = 0, average.y = 0;
			for (int i = 0; i < sz; i++)
			{
				average.x += path[i].x;
				average.y += path[i].y;
			}
			average.x /= (double)sz;
			average.y /= (double)sz;
		}
		else if (path.size() >= 2)//�����ҽ�Զ�ĵ㣬����double��int����Ӧ���µĽǶȲ�׼
			average = path[1];
		else
			average = path[0];
		pace.x = average.x - info.self.xy_pos.x, pace.y = average.y - info.self.xy_pos.y;
		idealMove = XYToPolar(average).angle;
		idealView = XYToPolar(dest).angle;
		if (f.mode == 2)//����������ӵ�
			idealMove = AngleLimit(idealMove - 90.0);
		else if (f.mode == 3)//�Һ��������ӵ�
			idealMove = AngleLimit(idealMove + 90.0);
		if (follow == 1)//follow = 1��תͷ���������յ�
			idealView = 100.0;
		return Move(idealMove, idealView, strong);
	}
	else
		return false;
}
void Do()//��ָ���¼�ɹ���������
{
	Thing tmp1, tmp2;
	while (DoFirstThing() == 0)
	{
		if (todo.empty())
			break;
		else
			todo.pop();
	}
	if (!todo.empty())
	{
		tmp1 = sucTodo1 = todo.top();//�洢���غϳɹ�������1
		destination = todo.top().destination;
		if (todo.top().type == HEAL || todo.top().type == SHOOT)
		{
			todo.pop();
			while (DoFirstThing() == 0)
			{
				if (todo.empty())
					break;
				else
					todo.pop();
			}
			if (!todo.empty())
			{
				tmp2 = sucTodo2 = todo.top();//�洢���غϳɹ�������2
				destination = todo.top().destination;
			}
		}
	}
	while (!todo.empty())//clear list
		todo.pop();
	if (tmp1.type == CHASE_ITEM)
	{
		tmp1.priority = 10 * (int)tmp1.type + 2;
		todo.push(tmp1);
	}
	if (tmp2.type == CHASE_ITEM)
	{
		tmp2.priority = 10 * (int)tmp2.type + 2;
		todo.push(tmp2);
	}
	if (tmp1.type == CHASE_ENEMY)
	{
		tmp1.priority = 10 * (int)tmp1.type + 5;
		todo.push(tmp1);
	}
	if (tmp2.type == CHASE_ENEMY)
	{
		tmp2.priority = 10 * (int)tmp2.type + 5;
		todo.push(tmp2);
	}
	if (tmp1.type != COLLECT && tmp2.type != COLLECT)
		RealShoot();
}
void Demand()//ˢ��demand��durability��totalHurt��totalHeal
{
	totalHurt = totalHeal = 0;
	for (int i = 0; i < 5; i++)
		demand[i] = 100;
	demand[5] = 0;
	memset(durability, 0, sizeof(durability));
	for (int i = 0; i < info.self.bag.size(); i++)
	{
		if (info.self.bag[i].durability > 0)
		{
			durability[info.self.bag[i].type] = info.self.bag[i].durability;
			switch (info.self.bag[i].type)
			{
			case 1:case 2:case 3:case 4:case 5:case 6:case 7:case 9:
				totalHurt += ITEM_DATA[info.self.bag[i].type].damage * info.self.bag[i].durability;
				demand[0] -= (int)((double)info.self.bag[i].durability / (double)ITEM_DATA[info.self.bag[i].type].durability * (double)UnitValue(info.self.bag[i].type) * 4);
				break;
			case 10:case 11:case 12:case 13:
				demand[1] -= (int)((double)info.self.bag[i].durability / (double)ITEM_DATA[info.self.bag[i].type].durability * (double)UnitValue(info.self.bag[i].type) * 2);
				break;
			case 14:
				demand[2] = 0;
				break;
			case 15:case 16:
				totalHeal -= (int)ITEM_DATA[info.self.bag[i].type].param * info.self.bag[i].durability;//param < 0
				demand[3] -= UnitValue(info.self.bag[i].type);
				break;
			default:
				break;
			}
		}
	}
	if (info.self.vocation != HACK)
		demand[4] = 0;
	for (int i = 0; i < 6; i++)
		if (demand[i] < 0)
			demand[i] = 0;
}
bool Neibour(XYPosition a, XYPosition b)
{
	return (Dist(a, b) <= 1.0);
}
int SeeEnemy()//����������򷵻�2������ûǹ���˷���1��û��������0
{
	int num, enemyNum = FindEnemyNum();
	if (!todo.empty() && todo.top().priority % 10 == 5)//��CHASE_ENEMY������CHASE_ENEMYӦ���ŵ��ˣ���������ϻغ�ִ���ˣ���غ���Ӧ�������ˣ���û������˵�����ڵ��򱻸����ˣ�����SeeEnemy�����ִ�еĺ���������Ӧ�ò����ܵ�����������е��¼�Ӱ�졣
	{
		int flg = 0;
		for (int i = 0; i < info.others.size(); i++)
		{
			if ((!IsFriend(info.others[i].player_ID)) && info.others[i].player_ID == todo.top().id && info.others[i].status != DEAD && info.others[i].status != REAL_DEAD)//�����ϻغϱ�ǵĵ�������û��
			{
				int mod, num = HaveWeapon(info.others[i].polar_pos.distance);
				Thing tmpt = todo.top();
				if (num < 0)//����ǹ�򲻵�����׷����Ϊ�п����������ܴ򵽵ĵ���
					break;
				todo.pop();
				if (!todoPrint.empty() && todoPrint.top().priority % 10 == 5)
					todoPrint.pop();
				if (info.others[i].polar_pos.distance > Min((double)ITEM_DATA[num].range, VOCATION_DATA[info.self.vocation].distance - 10.0))//���ܴ򵽵������Զ����Ҫ׷��
					mod = 1;//1:׷��
				else
					mod = 2 + rand() % 2;//2:��������۾�����,3:�Һ������۾�����
				tmpt.destination = PolarToXY(info.others[i].polar_pos);
				tmpt.mode = mod;//ˢ��mode�͵�������
				todo.push(tmpt);
				todoPrint.push(tmpt);
				enemyNum = i;
				flg = 1;
				break;
			}
		}
		if (flg != 1)
		{
			todo.pop();
			if (!todoPrint.empty() && todoPrint.top().priority % 10 == 5)
				todoPrint.pop();
		}
	}
	if (info.others.empty())
		return 0;
	if (enemyNum < 0)
		return 0;
	if (HaveWeapon() <= 0)//ûǹ���� 
		return 1;
	num = HaveWeapon(info.others[enemyNum].polar_pos.distance);
	if (num >= 0)
	{
		int mod;
		if (info.others[enemyNum].status == MOVING || info.others[enemyNum].status == MOVING_SHOOTING)
		{
			double l = info.others[enemyNum].move_speed * predictEnemyPace;
			if (landform[LimitBound((int)(PolarToXY(info.others[enemyNum].polar_pos).x))][LimitBound((int)(PolarToXY(info.others[enemyNum].polar_pos).y))] == 2)
				l *= 0.6;
			enemyPace.x = l * cos(info.others[enemyNum].move_angle * pi / 180.0);//Ԥ�����λ��
			enemyPace.y = l * sin(info.others[enemyNum].move_angle * pi / 180.0);
		}//Ԥ��
		todo.push(Thing(SHOOT, PolarToXY(info.others[enemyNum].polar_pos), (ITEM)num, info.others[enemyNum].polar_pos.angle, info.others[enemyNum].player_ID));//��ʱidΪʹ�õ�ǹ֧���
		todoPrint.push(Thing(SHOOT, PolarToXY(info.others[enemyNum].polar_pos), (ITEM)num, info.others[enemyNum].polar_pos.angle, info.others[enemyNum].player_ID));
		if (info.others[enemyNum].polar_pos.distance > Min((double)ITEM_DATA[num].range, VOCATION_DATA[info.self.vocation].distance - 10.0))//���ܴ򵽵������Զ����Ҫ׷��
			mod = 1;//1��׷��
		else if (info.others[enemyNum].polar_pos.distance < 10.0)//�������Լ��ܽ�����Ҫ���Һ���������
			mod = 2 + rand() % 2;//2����������۾�����,3���Һ������۾�����
		Thing tmpt(CHASE_ENEMY, PolarToXY(info.others[enemyNum].polar_pos), info.others[enemyNum].player_ID);
		tmpt.mode = mod;
		todo.push(tmpt);
		todoPrint.push(tmpt);
	}
	else if (HaveWeapon(info.others[enemyNum].polar_pos.distance - 10.0) >= 0)//������̷�Χ��̫Զ
	{
		Thing tmpt(CHASE_ENEMY, PolarToXY(info.others[enemyNum].polar_pos), info.others[enemyNum].player_ID);
		tmpt.mode = 1;//1��׷��
		todo.push(tmpt);
		todoPrint.push(tmpt);
	}
	return 2;//��ǹ���򲻵��Ͳ�׷�ˣ���ϵ����
}
bool CanChange(XYPosition p, ITEM i)//�ж��Ƿ���Ը�����������Ʒ
{
	for (int i = 0; i < change.size(); i++)
		if (Neibour(change[i].pos, p) && change[i].type == i)
			return false;
	return true;
}
int CollectGarbage()//����
{
	if (inside < 2)
		return 0;
	double minDist = 100000.0;
	int num = -1;
	double relativeAng = -1.0;
	if (!todo.empty() && todo.top().priority % 10 == 2)
		relativeAng = XYToPolar(todo.top().destination).angle;
	if (relativeAng >= 180.0)
		relativeAng = 360.0 - relativeAng;
	if (relativeAng >= 0.0 && relativeAng <= ((VOCATION_DATA[info.self.vocation].angle / 2.0)) && !Intersect(info.self.xy_pos, AngleLimit(XYToPolar(destination).angle + nowViewAng), 0.0, Dist(info.self.xy_pos, destination)))//�ճ�תͷʱ��ʱ����
	{
		int flg = 0;
		for (int i = 0; i < info.items.size(); i++)
		{
			if (Neibour(destination, PolarToXY(info.items[i].polar_pos)) && UnitValue(info.items[i].type) > 0 && InPoison(PolarToXY(info.items[i].polar_pos)) == 2)//��Ҫ��dest����������Ȧ��
			{
				flg = 1;
				break;
			}
		}//��ѭ��˵��destination���Ƕ������߶�����������
		if (flg == 0 && (!todo.empty()) && todo.top().priority % 10 == 2)//û������˵���Ѿ�������
		{
			todo.pop();
			if (!todoPrint.empty() && todoPrint.top().priority % 10 == 2)
				todoPrint.pop();
		}
	}
	if (!Neibour(info.self.xy_pos, destination))//��û��dest
	{
		num = FindGarbageNum();
		if (num >= 0)
		{
			if (!todo.empty() && todo.top().priority % 10 == 2 && CanChange(PolarToXY(info.items[num].polar_pos), info.items[num].type) && Priority(todo.top().item, info.items[num].type, 0, 0, 1))//������Ʒ
			{
				Thing tmpt(CHASE_ITEM, PolarToXY(info.items[num].polar_pos), info.items[num].type);
				tmpt.priority = 10 * (int)tmpt.type + 3;
				if (CanChange(todo.top().destination, todo.top().item))//���ظ�
					change.push_back(ChangedItem(todo.top().destination, todo.top().item));
				todo.push(tmpt);
				todoPrint.push(tmpt);
				return 1;
			}
			else
			{
				todo.push(Thing(CHASE_ITEM, PolarToXY(info.items[num].polar_pos), info.items[num].type));
				todoPrint.push(Thing(CHASE_ITEM, PolarToXY(info.items[num].polar_pos), info.items[num].type));
				return 1;
			}
		}
		else
			return 0;
	}
	else//�Ѿ���destination��
	{
		for (int i = 0; i < info.items.size(); i++)
		{
			if (Neibour(info.self.xy_pos, PolarToXY(info.items[i].polar_pos)) && UnitValue(info.items[i].type) > 0)//��Ҫ�ҹ��õ�
			{
				todo.push(Thing(COLLECT, info.items[i].item_ID, info.items[i].type));
				todoPrint.push(Thing(COLLECT, info.items[i].item_ID, info.items[i].type));
				change.clear();
				return 2;
			}
		}//��ѭ��˵�����������߹��ˣ���Ӧ�ó��֣�
		if (!todo.empty() && todo.top().priority % 10 == 2)
		{
			todo.pop();
			if ((!todoPrint.empty()) && todoPrint.top().priority % 10 == 2)
				todoPrint.pop();
		}
		num = FindGarbageNum();
		if (num >= 0)
		{
			todo.push(Thing(CHASE_ITEM, PolarToXY(info.items[num].polar_pos), info.items[num].type));
			todoPrint.push(Thing(CHASE_ITEM, PolarToXY(info.items[num].polar_pos), info.items[num].type));
			return 1;
		}
		else
			return 0;
	}
}
void Heal()//����
{
	if (frame < 2 || info.self.status == ON_PLANE || info.self.status == JUMPING)
		return;
	if (fabs(info.self.hp_limit - info.self.hp >= 15.0) && fabs(info.self.hp_limit - info.self.hp < 65.0))//��Ѫ������
	{
		if ((!todo.empty() && todo.top().type != SHOOT) || todo.empty())//���ڴ�������ñ���
		{
			for (int i = 0; i < info.self.bag.size(); i++)
			{
				if (info.self.bag[i].type == 15 && info.self.bag[i].durability > 0)
				{
					todo.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0));
					todoPrint.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0));
					return;
				}
			}
		}
		else//���ʱ������ҽ����
		{
			for (int i = 0; i < info.self.bag.size(); i++)
			{
				if (info.self.bag[i].type == 16 && info.self.bag[i].durability > 0)
				{
					todo.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
					todoPrint.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
					return;
				}
			}
			for (int i = 0; i < info.self.bag.size(); i++)
			{
				if (info.self.bag[i].type == 15 && info.self.bag[i].durability > 0)
				{
					todo.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
					todoPrint.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
					return;
				}
			}
		}
	}
	else if (fabs(info.self.hp_limit - info.self.hp >= 65.0))//��Ѫ������������ҽ����
	{
		for (int i = 0; i < info.self.bag.size(); i++)
		{
			if (info.self.bag[i].type == 16 && info.self.bag[i].durability > 0)
			{
				todo.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
				todoPrint.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
				return;
			}
		}
		for (int i = 0; i < info.self.bag.size(); i++)
		{
			if (info.self.bag[i].type == 15 && info.self.bag[i].durability > 0)
			{
				todo.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
				todoPrint.push(Thing(HEAL, info.self.xy_pos, info.self.bag[i].type, 0.0, 100));
				return;
			}
		}
	}
}
void YYX()//�ܶ���˵������û����񫣡������
{
	if (frame < 2 || info.self.status == ON_PLANE || info.self.status == JUMPING)
		return;
	inside = InPoison(info.self.xy_pos);
	if (inside < 2)//������һ��Ȧ���Ľ�Զ���ܶ�
	{
		todo.push(Thing(RUN, info.poison.next_center));
		todoPrint.push(Thing(RUN, info.poison.next_center));
		return;
	}
	XYPosition tmp = destination;
	if (frame <= 200)
	{
		XYPosition org;
		org.x = org.y = 500.0;
		if (!(Dist(destination, org) < 200.0 && Dist(destination, info.self.xy_pos) > 10.0 && landform[(int)destination.x][(int)destination.y] != 2))//des������
		{
			double alpha = (double)(rand() % 16384) * pi / 8192.0;//���˦�Ƕȣ���һ���Ե�ͼ����ΪԲ�ģ�180Ϊ�뾶��Բ��һ��
			tmp.x = LimitBound(org.x + 180.0 * cos(alpha));
			tmp.y = LimitBound(org.y + 180.0 * sin(alpha));
			tmp = finder.SearchAccess(tmp);//��һ���ܵ����Ŀ���
		}
	}
	else if (info.poison.next_radius > 120)//Ȧ���ϴ�
	{
		if (!(Dist(destination, info.poison.next_center) < 0.75 * info.poison.next_radius && Dist(destination, info.self.xy_pos) > 10.0 && landform[LimitBound((int)destination.x)][LimitBound((int)destination.y)] != 2))//des������
		{
			double alpha = (double)(rand() % 16384) * pi / 8192.0;//���˦�Ƕȣ���һ������һ��Ȧ����ΪԲ�ģ�0.6 * ��һ��Ȧ�뾶��Բ��һ��
			tmp.x = LimitBound(info.poison.next_center.x + 0.6 * info.poison.next_radius * cos(alpha));
			tmp.y = LimitBound(info.poison.next_center.y + 0.6 * info.poison.next_radius * sin(alpha));
			tmp = finder.SearchAccess(tmp);//��һ���ܵ����Ŀ���
		}
	}
	else
	{
		if (!(Dist(destination, info.poison.next_center) < 0.5 * info.poison.next_radius && Dist(destination, info.self.xy_pos) > 7.0 && landform[LimitBound((int)destination.x)][LimitBound((int)destination.y)] != 2))//des������
		{
			double alpha = (double)(rand() % 16384) * pi / 8192.0;//���˦�Ƕȣ���һ������һ��Ȧ����ΪԲ�ģ�0.5 * ��һ��Ȧ�뾶��Բ��һ��
			tmp.x = LimitBound(info.poison.next_center.x + 0.5 * info.poison.next_radius * cos(alpha));
			tmp.y = LimitBound(info.poison.next_center.y + 0.5 * info.poison.next_radius * sin(alpha));
			tmp = finder.SearchAccess(tmp);//��һ���ܵ����Ŀ���
		}
	}
	todo.push(Thing(WANDER, tmp));
	todoPrint.push(Thing(WANDER, tmp));
}
void FprintItem(FILE *fp, ITEM t)
{
	switch (t)
	{
	case HAND_GUN:
		fprintf(fp, "    USP    ");
		break;
	case SUBMACHINE_GUN:
		fprintf(fp, "    P90    ");
		break;
	case SEMI_AUTOMATIC_RILE:
		fprintf(fp, "    SKS    ");
		break;
	case ASSAULT_RIFLE:
		fprintf(fp, "    AK47   ");
		break;
	case MACHINE_GUN:
		fprintf(fp, "    M249   ");
		break;
	case SNIPER_RILFE:
		fprintf(fp, "    AWP    ");
		break;
	case SNIPER_BARRETT:
		fprintf(fp, "  Barrett  ");
		break;
	case TIGER_BILLOW_HAMMER:
		fprintf(fp, "   Hammer  ");
		break;
	case CROSSBOW:
		fprintf(fp, " Cross Bow ");
		break;
	case VEST_1:
		fprintf(fp, "   Vest 1  ");
		break;
	case VEST_2:
		fprintf(fp, "   Vest 2  ");
		break;
	case VEST_3:
		fprintf(fp, "   Vest 3  ");
		break;
	case INSULATED_CLOTHING:
		fprintf(fp, "   Vest E  ");
		break;
	case MUFFLER:
		fprintf(fp, "  Muffler  ");
		break;
	case BONDAGE:
		fprintf(fp, "  Bandage  ");
		break;
	case FIRST_AID_CASE:
		fprintf(fp, "  Aid Case ");
		break;
	case CODE_CASE:
		fprintf(fp, "   Code    ");
		break;
	case SCOPE_2:
		fprintf(fp, "  Scope 2  ");
		break;
	case SCOPE_4:
		fprintf(fp, "  Scope 4  ");
		break;
	case SCOPE_8:
		fprintf(fp, "  Scope 8  ");
		break;
	default:
		fprintf(fp, "           ");
		break;
	}
}
void FprintThing(FILE *fp, Thing a)
{
	switch (a.type)
	{
	case SHOOT:
		fprintf(fp, "SHOOT       ");
		break;
	case HEAL:
		fprintf(fp, "HEAL        ");
		break;
	case COLLECT:
		fprintf(fp, "COLLECT     ");
		break;
	case CHASE_ENEMY:
		fprintf(fp, "CHASE_ENEMY ");
		break;
	case RUN:
		fprintf(fp, "RUN         ");
		break;
	case CHASE_ITEM:
		fprintf(fp, "CHASE_ITEM  ");
		break;
	case WANDER:
		fprintf(fp, "WANDER      ");
		break;
	}
	fprintf(fp, "%5.1f    %5.1f    %5.1f    ", a.destination.x, a.destination.y, a.ang);
	FprintItem(fp, a.item);
	fprintf(fp, "    %d      %2d", a.id, a.priority);
}
void File()
{
	int tfs = clock();
	FILE *fp;
	char round[100];
	static int first = 0;
	if (frame == 0)
		return;
	switch (info.self.vocation)
	{
	case MEDIC:
		sprintf(round, "C:\\Users\\123\\Desktop\\%dmedic%d.txt", info.player_ID, info.player_ID / 4 + 1);
		break;
	case HACK:
		sprintf(round, "C:\\Users\\123\\Desktop\\%dhack%d.txt", info.player_ID, info.player_ID / 4 + 1);
		break;
	case SIGNALMAN:
		sprintf(round, "C:\\Users\\123\\Desktop\\%dsignalman%d.txt", info.player_ID, info.player_ID / 4 + 1);
		break;
	default://case SNIPER:
		sprintf(round, "C:\\Users\\123\\Desktop\\%dsniper%d.txt", info.player_ID, info.player_ID / 4 + 1);
		break;
	}
	if (first == 0)
	{
		first = 1;
		fp = fopen(round, "w");
	}
	else
		fp = fopen(round, "a+");
	fprintf(fp, "f=%d, enmey:%d, garbage:%d, path:%lu, delay:%d, follow:%d, hurt:%d, heal:%d\n", frame, seeEnemy, collectGarbage, path.size(), delay, follow, totalHurt, totalHeal);
	fprintf(fp, "Heal:%6.1f /%6.1f  Pos :%6.3f %6.3f\n", info.self.hp, info.self.hp_limit, info.self.xy_pos.x, info.self.xy_pos.y);
	fprintf(fp, "Cen :%6.1f ,%6.1f  Next:%6.1f ,%6.1f           ", info.poison.current_center.x, info.poison.current_center.y, info.poison.next_center.x, info.poison.next_center.y);
	int xx = (int)info.self.xy_pos.x, yy = (int)info.self.xy_pos.y;
	int xmin = LimitBound(xx - 2), xmax = LimitBound(xx + 2), y = LimitBound(yy + 2);
	for (int i = xmin; i <= xmax; i++)
		fprintf(fp, "%d  ", landform[i][y]);
	y = LimitBound(yy + 1);
	fprintf(fp, "\nRad :%6.1f ,%6.1f  Rest:%6d ", info.poison.current_radius, info.poison.next_radius, info.poison.rest_frames);
	if (info.poison.move_flag == 3)
		fprintf(fp, "to point          ");
	if (info.poison.move_flag == 2)
		fprintf(fp, "to move           ");
	else if (info.poison.move_flag == 1)
		fprintf(fp, "to finish         ");
	else
		fprintf(fp, "to start          ");
	for (int i = xmin; i <= xmax; i++)
		fprintf(fp, "%d  ", landform[i][y]);
	y = LimitBound(yy);
	fprintf(fp, "\nAng :%6.1f ,%6.1f  Stat:%6d     ", info.self.move_angle, info.self.view_angle, inside);
	switch (info.self.status)
	{
	case RELAX:
		fprintf(fp, "Relax         "); break;
	case ON_PLANE:
		fprintf(fp, "Fly           "); break;
	case JUMPING:
		fprintf(fp, "Jump          "); break;
	case MOVING:
		fprintf(fp, "Move          "); break;
	case SHOOTING:
		fprintf(fp, "Shoot         "); break;
	case MOVING_SHOOTING:
		fprintf(fp, "Mv&St         "); break;
	case DEAD:
		fprintf(fp, "Dying         "); break;
	case REAL_DEAD:
		fprintf(fp, "Dead          "); break;
	}
	for (int i = xmin; i <= xmax; i++)
		fprintf(fp, "%d  ", landform[i][y]);
	y = LimitBound(yy - 1);
	fprintf(fp, "\nToCr:%6.1f ,%6.1f  Dest:%6.1f ,%6.1f           ", Dist(info.self.xy_pos, info.poison.current_center) - info.poison.current_radius, Dist(info.self.xy_pos, info.poison.next_center) - info.poison.next_radius, destination.x, destination.y);
	for (int i = xmin; i <= xmax; i++)
		fprintf(fp, "%d  ", landform[i][y]);
	y = LimitBound(yy - 2);
	fprintf(fp, "\nShrk:%6.1f ,%6.1f  Dist:%6.1f                   ", shrink.x, shrink.y, Dist(info.self.xy_pos, destination));
	for (int i = xmin; i <= xmax; i++)
		fprintf(fp, "%d  ", landform[i][y]);
	fprintf(fp, "\nPace:%6.3lf ,%6.3lf  IdAg:%6.1f ,%6.1f", pace.x, pace.y, AngleLimit(idealMove + nowViewAng), AngleLimit(nowViewAng + idealView));
	fprintf(fp, "\nAtCd:%3d ,MvCd:%3d", info.self.attack_cd, info.self.move_cd);
	fprintf(fp, "\nMyPc:%6.4f ,%6.4f  EnPc:%6.4f ,%6.4f", myPace.x, myPace.y, enemyPace.x, enemyPace.y);
	fprintf(fp, "\nPredictPos:%6.3f ,%6.3f  gras:%6.1f ,%6.1f", info.self.xy_pos.x + myPace.x, info.self.xy_pos.y + myPace.y, grassPos.x, grassPos.y);
	int fst = 0;
	for (int i = 0; i < info.others.size(); i++)
		if ((!IsFriend(info.others[i].player_ID)) && info.others[i].status != DEAD && info.others[i].status != REAL_DEAD)
		{
			if (fst == 0)
			{
				fst = 1;
				fprintf(fp, "\n---------------------------------------------------------------------------------\n");
				fprintf(fp, "num,   speed,  moveAng,   viewAng,     dist,       x,         y,         id");
			}
			fprintf(fp, "\nenemy:%5.1f, %9.3f, %9.3f, %9.3f, %9.3f, %9.3f, %7d", info.others[i].move_speed, info.others[i].move_angle,
				AngleLimit(info.self.view_angle + info.others[i].polar_pos.angle), info.others[i].polar_pos.distance,
				PolarToXY(info.others[i].polar_pos, false).x, PolarToXY(info.others[i].polar_pos, false).y, info.others[i].player_ID);
		}
	fst = 0;
	fprintf(fp, "\npath: ");
	for (int i = 0; i < Min(6, (int)path.size()); i++)
		fprintf(fp, "%d:%5.1f, %5.1f ", i, path[i].x, path[i].y);
	fprintf(fp, "\nchange: ");
	for (int i = 0; i < change.size(); i++)
	{
		fprintf(fp, "\n%d: %5.1f, %5.1f  ", i + 1, change[i].pos.x, change[i].pos.y);
		FprintItem(fp, change[i].type);
	}
	for (int i = 1; i < ITEM_SZ; i++)
		if (durability[i] > 0)
		{
			if (fst == 0)
			{
				fst = 1;
				fprintf(fp, "\n---------------------------------------------------------------------------------");
			}
			fprintf(fp, "\n");
			FprintItem(fp, (ITEM)i);
			fprintf(fp, "  %8d   %10d%%", durability[i], (100 * durability[i]) / ITEM_DATA[i].durability);
		}
	fst = 0;
	while (!todoPrint.empty())
	{
		if (fst == 0)
		{
			fst = 1;
			fprintf(fp, "\n---------------------------------------------------------------------------------\n");
			fprintf(fp, " type         x        y       ang         item      id      prio\n");
		}
		FprintThing(fp, todoPrint.top());
		if (sucTodo1 == todoPrint.top() || sucTodo2 == todoPrint.top())
			fprintf(fp, "       Execute\n");
		else
			fprintf(fp, "\n");
		todoPrint.pop();
	}
	if (sucTodo1.type == CHASE_ITEM)
	{
		sucTodo1.priority = 10 * (int)sucTodo1.type + 2;
		todoPrint.push(sucTodo1);
	}
	if (sucTodo2.type == CHASE_ITEM)
	{
		sucTodo2.priority = 10 * (int)sucTodo2.type + 2;
		todoPrint.push(sucTodo2);
	}
	if (sucTodo1.type == CHASE_ENEMY)
	{
		sucTodo1.priority = 10 * (int)sucTodo1.type + 5;
		todoPrint.push(sucTodo1);
	}
	if (sucTodo2.type == CHASE_ENEMY)
	{
		sucTodo2.priority = 10 * (int)sucTodo2.type + 5;
		todoPrint.push(sucTodo2);
	}
	static XYPosition t1, t2, predict;
	if (frame == 0)
	{
		t1.x = t1.y = t2.x = t2.y = 0.0;
		predict = info.self.xy_pos;
	}
	if (info.self.status != DEAD && info.self.status != REAL_DEAD && DoubleEqual(t1.x, info.self.xy_pos.x, 0.1)
		&& DoubleEqual(t1.y, info.self.xy_pos.y, 0.1) && DoubleEqual(t2.x, info.self.xy_pos.x, 0.1)
		&& DoubleEqual(t2.y, info.self.xy_pos.y, 0.1) && DoubleEqual(t1.x, t2.x, 0.1) && DoubleEqual(t1.y, t2.y, 0.1))
	{
		if (info.self.status == SHOOTING)
			fprintf(fp, "ShootStuck!!!!\n");
		else
			fprintf(fp, "RealStuck!!!!\n");
	}
	fprintf(fp, "PreL:%4.2f, delta:%4.2f, ReaL%4.2f\n", Dist(predict, t1), Dist(predict, info.self.xy_pos), Dist(t1, info.self.xy_pos));
	if (info.self.status != DEAD && info.self.status != REAL_DEAD && info.self.status != JUMPING && info.self.status != ON_PLANE && info.self.status != RELAX && Dist(info.self.xy_pos, predict) >= 0.08)
		fprintf(fp, "predictLost!\n");
	t2 = t1;
	t1 = info.self.xy_pos;
	predict.x = info.self.xy_pos.x + myPace.x;
	predict.y = info.self.xy_pos.y + myPace.y;
	if (delay > 20)
		fprintf(fp, "TimeDanger!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
	tfs = clock() - tfs;
	if (tfs + delay > 40)
		fprintf(fp, "%d RealTimeDanger!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n", tfs + delay);
	fprintf(fp, "\n========================================================================================================\n");
	fclose(fp);
}
void play_game()
{
	bool printLog = 0;
	delay = clock();
	Initial(MEDIC);//�ķݴ���ֻ����Ĵ˴�ѡ��MEDIC, SIGNALMAN, HACK, SNIPER
	Demand();
	seeEnemy = SeeEnemy();
	collectGarbage = CollectGarbage();
	YYX();
	Heal();
	Do();
	delay = clock() - delay;
	if(printLog)
		File();
	else
		while (!todoPrint.empty())
			todoPrint.pop();
}