#include <stdio.h>
#include <algorithm>
#include <string>
#include <vector>

using namespace std;

class Block {
public:
	Block(int n) : name(n) {}

	int name;
	vector<Block*> in;
	vector<Block*> out;

	string String();
	void Dump(FILE*);
};

string Block::String() {
	char buf[20];
	snprintf(buf, sizeof buf, "b%d", this->name);
	return buf;
}

void Block::Dump(FILE *f) {
	fprintf(f, "%s: [", this->String().c_str());
	for (int i = 0; i < this->in.size(); i++)
		fprintf(f, "%s%s", i > 0 ? " " : "", this->in[i]->String().c_str());
	fprintf(f, "] [");
	for (int i = 0; i < this->out.size(); i++)
		fprintf(f, "%s%s", i > 0 ? " " : "", this->out[i]->String().c_str());
	fprintf(f, "]\n");
}

struct Edge {
	Edge(int s, int d) : src(s), dst(d) {}
	int src, dst;
};

class CFG {
public:
	vector<Block*> block;
	vector<Edge> edge;

	Block *NewBlock();
	void Connect(Block *src, Block *dst);
	Block *Path(Block *from);
	Block *Diamond(Block *from);
	Block *BaseLoop(Block *from);
	void Dump(FILE*);
};

Block *CFG::NewBlock() {
	Block *b = new Block(this->block.size());
	this->block.push_back(b);
	return b;
}

void CFG::Dump(FILE *f) {
	for (int i = 0; i < this->block.size(); i++)
		this->block[i]->Dump(f);
}

void CFG::Connect(Block *src, Block *dst) {
	src->out.push_back(dst);
	dst->in.push_back(src);
	this->edge.push_back(Edge(src->name, dst->name));
}

Block *CFG::Path(Block *from) {
	Block *n = this->NewBlock();
	this->Connect(from, n);
	return n;
}

Block *CFG::Diamond(Block *from) {
	Block *x = this->Path(from);
	Block *y = this->Path(from);
	Block *z = this->Path(x);
	this->Connect(y, z);
	this->Connect(z, from);
	return z;
}

Block *CFG::BaseLoop(Block *from) {
	Block *z = this->Path(this->Diamond(this->Path(this->Diamond(this->Path(from)))));
	this->Connect(z, from);
	return this->Path(z);
}

CFG *BuildGraph() {
	CFG *g = new CFG;
	
	Block *n0 = g->NewBlock();
	Block *n1 = g->NewBlock();
	Block *n2 = g->NewBlock();
	g->Connect(n0, n2);
	
	for (int i = 0; i < 10; i++) {
		Block *n = g->NewBlock();
		g->Connect(n2, n);

		for (int j = 0; j < 100; j++) {
			Block *top = n;
			n = g->Path(n);
			for (int k = 0; k < 25; k++) {
				n = g->BaseLoop(n);
			}
			Block *bottom = g->Path(n);
			g->Connect(n, top);
			n = bottom;
		}
		g->Connect(n, n1);
	}
	return g;
}

// Basic representation of loop graph.

class Loop {
public:
	vector<Block*> block;
	vector<Loop*> child;
	Loop *parent;
	Block *head;
	
	bool isRoot;
	bool isReducible;
	int counter;
	int nesting;
	int depth;

};

class LoopGraph {
public:
	Loop root;
	vector<Loop*> loop;
	~LoopGraph();

	Loop *NewLoop(int cap);
	void CalculateNesting();
	void calculateNesting(Loop* l, int depth);
};

LoopGraph::~LoopGraph() {
	for (int i = 0; i < this->loop.size(); i++)
		delete this->loop[i];
}

static int loopCounter = 0;

Loop *LoopGraph::NewLoop(int cap) {
	loopCounter++;
	Loop *l = new Loop;
	l->counter = loopCounter;
	l->block.reserve(cap);
	this->loop.push_back(l);
	return l;
}

void LoopGraph::CalculateNesting() {
	for (int i = 0; i < this->loop.size(); i++) {
		Loop *l = this->loop[i];
		if (l->isRoot)
			continue;
		if (l->parent == NULL) {
			l->parent = &this->root;
			this->root.child.push_back(l);
		}
	}
	this->calculateNesting(&this->root, 0);
}

void LoopGraph::calculateNesting(Loop *l, int depth) {
	l->depth = depth;
	for (int i = 0; i < l->child.size(); i++) {
		Loop *child = l->child[i];
		this->calculateNesting(child, depth+1);
		int n = child->nesting + 1;
		if (l->nesting < n)
			l->nesting = n;
	}
}

// TODO: Dump, String

// Loop finding state, generated or reused on each iteration.

class LoopBlock {
public:
	enum Type {
		NonHeader,
		Reducible,
		Self,
		Irreducible,
		Dead,
	};

	Block *block;
	Loop *loop;
	int first;
	int last;
	LoopBlock *header; // TODO: head
	Type type;
	vector<LoopBlock*> backPred;
	vector<LoopBlock*> nonBackPred;
	LoopBlock *unionf;

	void Init(Block*);
	LoopBlock *Find();
	bool IsAncestor(LoopBlock*);
	
};

class LoopFinder {
public:
	vector<LoopBlock> loopBlock;
	vector<LoopBlock*> depthFirst;
	vector<LoopBlock*> pool;

	void Search(Block*);
	void FindLoops(CFG*, LoopGraph*);
};

const int Unvisited = -1;

void LoopBlock::Init(Block *b) {
	this->block = b;
	this->loop = NULL;
	this->first = Unvisited;
	this->last = Unvisited;
	this->header = NULL;
	this->type = LoopBlock::NonHeader;
	this->backPred.clear();
	this->nonBackPred.clear();
	this->unionf = this;
}

LoopBlock *LoopBlock::Find() {
	if (this->unionf != this) {
		this->unionf = this->unionf->Find();
	}
	return this->unionf;
}

// Depth first search to number blocks.

void LoopFinder::Search(Block *b) {
	LoopBlock *lb = &this->loopBlock[b->name];
	this->depthFirst.push_back(lb);
	lb->first = this->depthFirst.size();
	for (int i = 0; i < b->out.size(); i++) {
		Block *out = b->out[i];
		if (this->loopBlock[out->name].first == Unvisited)
			this->Search(out);
	}
	lb->last = this->depthFirst.size();
}

bool LoopBlock::IsAncestor(LoopBlock *p) {
	return this->first <= p->first && p->first <= this->last;
}

void LoopFinder::FindLoops(CFG *g, LoopGraph *lsg) {
	int size = g->block.size();
	if (size == 0)
		return;

	// Step A: Initialize nodes, depth first numbering, mark dead nodes.
	this->loopBlock.resize(size);
	this->depthFirst.reserve(size);
	this->depthFirst.clear();
	for (int i = 0; i < size; i++)
		this->loopBlock[i].Init(g->block[i]);
	this->Search(g->block[0]);
	for (int i = 0; i < size; i++ ){
		LoopBlock *lb = &this->loopBlock[i];  // TODO
		if (lb->first == Unvisited)
			lb->type = LoopBlock::Dead;
	}

	// Step B: Classify back edges as coming from descendents or not.
	for (int i = 0; i < this->depthFirst.size(); i++) {
		LoopBlock *lb = this->depthFirst[i];
		for (int j = 0; j < lb->block->in.size(); j++) {
			Block *b = lb->block->in[j];
			LoopBlock *lbb = &this->loopBlock[b->name];  // TODO
			if (lb->IsAncestor(lbb))
				lb->backPred.push_back(lbb);
			else
				lb->nonBackPred.push_back(lbb);
		}
	}

	// Start node is root of all other loops.
	this->loopBlock[0].header = &this->loopBlock[0];

	// Step C:
	//
	// The outer loop, unchanged from Tarjan. It does nothing except
	// for those nodes which are the destinations of backedges.
	// For a header node w, we chase backward from the sources of the
	// backedges adding nodes to the set P, representing the body of
	// the loop headed by w.
	//
	// By running through the nodes in reverse of the DFST preorder,
	// we ensure that inner loop headers will be processed before the
	// headers for surrounding loops.
	for (int i = this->depthFirst.size() - 1; i >= 0; i--) {
		LoopBlock *w = this->depthFirst[i];

		this->pool.clear();

		// Step D.
		for (int i = 0; i < w->backPred.size(); i++) {
			LoopBlock* pred = w->backPred[i];
			if (w == pred) {
				w->type = LoopBlock::Self;
				continue;
			}
			this->pool.push_back(pred->Find());
		}

		// Process node pool in order as work list.
		for (int i = 0; i < this->pool.size(); i++) {
			LoopBlock *x = this->pool[i];

			// Step E:
			//
			// Step E represents the main difference from Tarjan's method.
			// Chasing upwards from the sources of a node w's backedges. If
			// there is a node y' that is not a descendant of w, w is marked
			// the header of an irreducible loop, there is another entry
			// into this loop that avoids w->
			for (int j = 0; j < x->nonBackPred.size(); j++) {
				LoopBlock *y = x->nonBackPred[j];
				LoopBlock *ydash = y->Find();
				if (!w->IsAncestor(ydash)) {
					w->type = LoopBlock::Irreducible;
					if (find(w->nonBackPred.begin(), w->nonBackPred.end(), y) == w->nonBackPred.end())
						w->nonBackPred.push_back(y);
				} else if (ydash != w) {
					if (find(this->pool.begin(), this->pool.end(), ydash) == this->pool.end())
						this->pool.push_back(ydash);
				}
			}
		}

		// Collapse/Unionize nodes in a SCC to a single node
		// For every SCC found, create a loop descriptor and link it in.
		if (this->pool.size() > 0 || w->type == LoopBlock::Self) {
			Loop *l = lsg->NewLoop(1 + pool.size());
			l->head = w->block;
			l->block.push_back(w->block);
			l->isReducible = w->type != LoopBlock::Irreducible;
			w->loop = l;

			// At this point, one can set attributes to the loop, such as:
			//
			// the bottom node:
			//    iter  = backPreds[w].begin();
			//    loop bottom is: nodes[iter].node);
			//
			// the number of backedges:
			//    backPreds[w].size()
			for (int i = 0; i < pool.size(); i++) {
				LoopBlock *node = pool[i];
				// Add nodes to loop descriptor.
				node->header = w;
				node->unionf = w;

				// Nested loops are not added, but linked together.
				if (node->loop != NULL) {
					node->loop->parent = l;
				} else {
					l->block.push_back(node->block);
				}
			}
		}
	}
}

// Main program.

int main() {
	LoopFinder f;
	
	CFG *g = BuildGraph();
	LoopGraph lsg;
	f.FindLoops(g, &lsg);
	
	for (int i = 0; i < 50; i++) {
		LoopGraph lsg;
		f.FindLoops(g, &lsg);
	}

	printf("# of loops: %d (including 1 artificial root node)\n", (int)lsg.loop.size());
	lsg.CalculateNesting();
}
