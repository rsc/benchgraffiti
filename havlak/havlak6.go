package main

import (
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"runtime/pprof"
)

// Control flow graph, created once.

type Block struct {
	Name int
	In   []*Block
	Out  []*Block
}

func (b *Block) String() string {
	return fmt.Sprintf("b%d", b.Name)
}

func (b *Block) Dump(w io.Writer) {
	fmt.Fprintf(w, "%s: %v %v\n", b, b.In, b.Out)
}

type CFG struct {
	Block []*Block
	Edge  []Edge
}

type Edge struct {
	Src, Dst int
}

func (g *CFG) NewBlock() *Block {
	b := &Block{Name: len(g.Block)}
	g.Block = append(g.Block, b)
	return b
}

func (g *CFG) Dump(w io.Writer) {
	for _, b := range g.Block {
		b.Dump(w)
	}
}

func (g *CFG) Connect(src, dst *Block) {
	src.Out = append(src.Out, dst)
	dst.In = append(dst.In, src)
	g.Edge = append(g.Edge, Edge{src.Name, dst.Name})
}

func (g *CFG) Path(from *Block) *Block {
	n := g.NewBlock()
	g.Connect(from, n)
	return n
}

func (g *CFG) Diamond(from *Block) *Block {
	x := g.Path(from)
	y := g.Path(from)
	z := g.Path(x)
	g.Connect(y, z)
	g.Connect(z, from)
	return z
}

func (g *CFG) BaseLoop(from *Block) *Block {
	z := g.Path(g.Diamond(g.Path(g.Diamond(g.Path(from)))))
	g.Connect(z, from)
	return g.Path(z)
}

func buildGraph() *CFG {
	g := new(CFG)

	n0 := g.NewBlock()
	n1 := g.NewBlock()
	n2 := g.NewBlock()
	g.Connect(n0, n2)

	for i := 0; i < 10; i++ {
		n := g.NewBlock()
		g.Connect(n2, n)

		for j := 0; j < 100; j++ {
			top := n
			n = g.Path(n)
			for k := 0; k < 25; k++ {
				n = g.BaseLoop(n)
			}
			bottom := g.Path(n)
			g.Connect(n, top)
			n = bottom
		}
		g.Connect(n, n1)
	}
	return g
}

// Basic representation of loop graph.

type LoopGraph struct {
	Root Loop
	Loop []*Loop
}

type Loop struct {
	Block  []*Block
	Child  []*Loop
	Parent *Loop
	Head   *Block

	IsRoot      bool
	IsReducible bool
	Counter     int
	Nesting     int
	Depth       int
}

var loopCounter = 0

func (g *LoopGraph) Clear() {
	g.Root.Child = g.Root.Child[:0]
	g.Loop = g.Loop[:0]
}	

func (g *LoopGraph) NewLoop(lcap int) *Loop {
	// If there's a cached loop, use that.
	if n := len(g.Loop); n  < cap(g.Loop) && g.Loop[:n+1][n] != nil {
		g.Loop = g.Loop[:n+1]
		l := g.Loop[n]
		l.Block = l.Block[:0]
		l.Child = l.Child[:0]
		l.Parent = nil
		l.Head = nil
		l.IsRoot = false
		l.IsReducible = false
		l.Nesting = 0
		l.Depth = 0
		return l
	}

	loopCounter++
	l := &Loop{Counter: loopCounter}
	g.Loop = append(g.Loop, l)
	l.Block = make([]*Block, 0, lcap)
	return l
}

func (g *LoopGraph) CalculateNesting() {
	for _, l := range g.Loop {
if l==nil {panic("nil l")}
		if l.IsRoot {
			continue
		}
		if l.Parent == nil {
			l.Parent = &g.Root
			g.Root.Child = append(g.Root.Child, l)
		}
	}
	g.calculateNesting(&g.Root, 0)
}

func (g *LoopGraph) calculateNesting(l *Loop, depth int) {
	l.Depth = depth
	for _, child := range l.Child {
		g.calculateNesting(child, depth+1)
		if n := child.Nesting + 1; l.Nesting < n {
			l.Nesting = n
		}
	}
}

func (g *LoopGraph) Dump(w io.Writer) {
	g.dump(w, &g.Root, 0)
}

func (g *LoopGraph) dump(w io.Writer, l *Loop, indent int) {
	l.Dump(w, indent)

	for _, child := range l.Child {
		g.dump(w, child, indent+1)
	}
}

func (l *Loop) String() string {
	return fmt.Sprintf("loop-%d", l.Counter)
}

func (l *Loop) Dump(w io.Writer, indent int) {
	fmt.Fprintf(w, "%*sloop-%d nest: %d depth %d",
		2*indent, l.Counter, l.Nesting, l.Depth)
	if !l.IsReducible {
		fmt.Fprintf(w, " (Irreducible)")
	}
	if len(l.Child) > 0 {
		fmt.Fprintf(w, " Children: %v", l.Child)
	}
	if len(l.Block) > 0 {
		fmt.Fprintf(w, "(")
		sep := ""
		for _, b := range l.Block {
			fmt.Fprint(w, sep, b)
			if b == l.Head {
				fmt.Fprint(w, "*")
			}
			sep = " "
		}
		fmt.Fprintf(w, ")")
	}
	fmt.Fprintf(w, "\n")
}

// Loop finding state, generated or reused on each iteration.

type LoopFinder struct {
	LoopBlock  []LoopBlock
	DepthFirst []*LoopBlock
	Pool       []*LoopBlock
}

const Unvisited = -1

type LoopType int

const (
	bbNonHeader   LoopType = 1 + iota // a regular BB
	bbReducible                       // reducible loop
	bbSelf                            // single BB loop
	bbIrreducible                     // irreducible loop
	bbDead                            // a dead BB
)

type LoopBlock struct {
	Block       *Block
	Loop        *Loop
	First       int
	Last        int
	Header      *LoopBlock
	Type        LoopType
	BackPred    []*LoopBlock
	NonBackPred []*LoopBlock

	Union *LoopBlock // union find
}

func (lb *LoopBlock) Init(b *Block) {
	lb.Block = b
	lb.Loop = nil
	lb.First = Unvisited
	lb.Last = Unvisited
	lb.Header = nil
	lb.Type = bbNonHeader
	lb.BackPred = lb.BackPred[:0]
	lb.NonBackPred = lb.NonBackPred[:0]
	lb.Union = lb
}

func (lb *LoopBlock) Find() *LoopBlock {
	if lb.Union != lb {
		lb.Union = lb.Union.Find()
	}
	return lb.Union
}

// Depth first search to number blocks.

func (f *LoopFinder) Search(b *Block) {
	lb := &f.LoopBlock[b.Name]
	f.DepthFirst = append(f.DepthFirst, lb)
	lb.First = len(f.DepthFirst)
	for _, out := range b.Out {
		if f.LoopBlock[out.Name].First == Unvisited {
			f.Search(out)
		}
	}
	lb.Last = len(f.DepthFirst)
}

func (lb *LoopBlock) IsAncestor(p *LoopBlock) bool {
	return lb.First <= p.First && p.First <= lb.Last
}

func (f *LoopFinder) FindLoops(g *CFG, lsg *LoopGraph) {
	size := len(g.Block)
	if size == 0 {
		return
	}

	// Step A: Initialize nodes, depth first numbering, mark dead nodes.
	if size <= cap(f.LoopBlock) {
		f.LoopBlock = f.LoopBlock[:size]
		f.DepthFirst = f.DepthFirst[:0]
	} else {
		f.LoopBlock = make([]LoopBlock, size)
		f.DepthFirst = make([]*LoopBlock, 0, size)
	}
	for i := range f.LoopBlock {
		f.LoopBlock[i].Init(g.Block[i])
	}
	f.Search(g.Block[0])
	for i := range f.LoopBlock {
		lb := &f.LoopBlock[i]
		if lb.First == Unvisited {
			lb.Type = bbDead
		}
	}

	// Step B: Classify back edges as coming from descendents or not.
	for _, lb := range f.DepthFirst {
		for _, b := range lb.Block.In {
			lbb := &f.LoopBlock[b.Name]
			if lb.IsAncestor(lbb) {
				lb.BackPred = append(lb.BackPred, lbb)
			} else {
				lb.NonBackPred = append(lb.NonBackPred, lbb)
			}
		}
	}

	// Start node is root of all other loops.
	f.LoopBlock[0].Header = &f.LoopBlock[0]

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
	for i := len(f.DepthFirst) - 1; i >= 0; i-- {
		w := f.DepthFirst[i]

		pool := f.Pool[:0]

		// Step D.
		for _, pred := range w.BackPred {
			if w == pred {
				w.Type = bbSelf
				continue
			}
			pool = append(pool, pred.Find())
		}

		// Process node pool in order as work list.
		for i := 0; i < len(pool); i++ {
			x := pool[i]

			// Step E:
			//
			// Step E represents the main difference from Tarjan's method.
			// Chasing upwards from the sources of a node w's backedges. If
			// there is a node y' that is not a descendant of w, w is marked
			// the header of an irreducible loop, there is another entry
			// into this loop that avoids w.
			for _, y := range x.NonBackPred {
				ydash := y.Find()
				if !w.IsAncestor(ydash) {
					w.Type = bbIrreducible
					w.NonBackPred = appendUnique(w.NonBackPred, y)
				} else if ydash != w {
					pool = appendUnique(pool, ydash)
				}
			}
		}

		// Collapse/Unionize nodes in a SCC to a single node
		// For every SCC found, create a loop descriptor and link it in.
		if len(pool) > 0 || w.Type == bbSelf {
			l := lsg.NewLoop(1 + len(pool))
			l.Head = w.Block
			l.Block = append(l.Block, w.Block)
			l.IsReducible = w.Type != bbIrreducible
			w.Loop = l

			// At this point, one can set attributes to the loop, such as:
			//
			// the bottom node:
			//    iter  = backPreds[w].begin();
			//    loop bottom is: nodes[iter].node);
			//
			// the number of backedges:
			//    backPreds[w].size()
			for _, node := range pool {
				// Add nodes to loop descriptor.
				node.Header = w
				node.Union = w

				// Nested loops are not added, but linked together.
				if node.Loop != nil {
					node.Loop.Parent = l
				} else {
					l.Block = append(l.Block, node.Block)
				}
			}
		}

		f.Pool = pool
	}
}

func appendUnique(pool []*LoopBlock, b *LoopBlock) []*LoopBlock {
	for _, p := range pool {
		if b == p {
			return pool
		}
	}
	return append(pool, b)
}

// Main program.

var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to this file")
var memprofile = flag.String("memprofile", "", "write memory profile to this file")
var reuseLoopGraph = flag.Bool("reuseloopgraph", true, "reuse loop graph memory")

func main() {
	flag.Parse()
	if *cpuprofile != "" {
		f, err := os.Create(*cpuprofile)
		if err != nil {
			log.Fatal(err)
		}
		pprof.StartCPUProfile(f)
		defer pprof.StopCPUProfile()
	}

	var f LoopFinder
	g := buildGraph()
	lsg := new(LoopGraph)
	f.FindLoops(g, lsg)

	if *memprofile != "" {
		f, err := os.Create(*memprofile)
		if err != nil {
			log.Fatal(err)
		}
		pprof.WriteHeapProfile(f)
		f.Close()
		return
	}

	for i := 0; i < 50; i++ {
		if *reuseLoopGraph {
			lsg.Clear()
			f.FindLoops(g, lsg)
		} else {
			f.FindLoops(g, new(LoopGraph))
		}
	}

	fmt.Printf("# of loops: %d (including 1 artificial root node)\n", len(lsg.Loop))
	lsg.CalculateNesting()
}
