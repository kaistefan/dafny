
/* Process Control Block*/
class PCB_t {
	var pid : int;
	var duration : int;
	var ownerID :int;
	var usedCPU : int;
	constructor Init (a: int, b: int,c:int)
	modifies this;
	ensures getPid() == a;
	ensures getDuration() == b;
	ensures getOwnerID() == c;
	ensures usedCPU == 0;
	{
		pid, duration,ownerID := a,b,c;
		usedCPU:=0;
	}
	function method getOwnerID () : int
	reads this;
	{
		ownerID
	}
	function method getPid () : int
	reads this;
	{
		pid
	}
	function method getDuration() : int
	reads this;
	{
		duration
	}
	function method getUsedCPU() : int
	reads this;
	{
		usedCPU
	}
}

class Queue  {

	var que : seq<PCB_t>;

	predicate Valid()
	reads this;
	reads que;
	{
		null !in que &&(forall i,j :: 0 <= i < j < |que| ==> que[i].getPid() != que[j].getPid())
	}
	predicate inQue(pid: int)
	requires Valid();
	reads this;
	reads que;
	{
		exists k: PCB_t :: k in que && k.getPid() == pid
	}
	constructor Init ()
	modifies this;
	ensures Valid();
	ensures que == [];
	{
		que := [];
	}

	method enQueue (a:PCB_t) 
	requires Valid();
	requires a!=null;
	requires !inQue(a.getPid());
	modifies this;
	ensures Valid();
	ensures |que|>0;
	ensures a == que[|que|-1];
	ensures |que| == old(|que|+1);
	ensures  que[..|que|-1]== old (que);
	{
		que:=que+[a];	
	}

	method deQueue ()  returns (a:PCB_t)
	requires Valid();
	requires |que|>0;
	modifies this;
	ensures Valid();
	ensures a == old(que[0]);
	ensures |que| == old(|que|)-1;
	ensures  que== old (que[1..]);
	{ 
		a:= que[0]; 
		que := que[1..];  
	}
	
}

class OS {
	var q1 : Queue;
	var pcb : PCB_t;
	var quantum : int;

	constructor Init(a: int)
	modifies this;
	ensures quantum == a;
	ensures q1 != null;
	{
		quantum := a;
		q1 := new Queue.Init();
	}

	method addPCB(a: PCB_t)
	requires q1 != null;
	requires a != null;
	requires q1.Valid();
	requires !q1.inQue(a.getPid());
	modifies q1;
	ensures q1.Valid();
	{
		q1.enQueue(a);
	}

	method getPCB() returns (a: PCB_t)
	requires q1 != null;
	requires pcb == null;
	requires q1.Valid();
	requires |q1.que| > 0;
	modifies this;
	modifies q1;
	ensures a == pcb;
	ensures q1 != null;
	ensures q1.Valid();
	
	{
		pcb := q1.deQueue();
		a := pcb;
	}

	method operate()
	requires q1 != null;
	requires pcb != null;
	requires q1.Valid();
	requires |q1.que| > 0;
	requires !q1.inQue(pcb.getPid());
	modifies this;
	modifies q1;
	modifies pcb;
	ensures pcb == null;
	ensures old (pcb.usedCPU + quantum < pcb.duration) ==> q1 != null && q1.Valid() && q1.inQue(old(pcb.getPid()));

	{
		pcb.usedCPU := pcb.usedCPU + quantum;
		if(pcb.usedCPU < pcb.duration) {
			q1.enQueue(pcb);
			assert q1.inQue(pcb.getPid());
		}
		pcb := null;
	}
}

method main () 
{
    var pcb1 := new PCB_t.Init(1,10,0);
	var pcb3 := new PCB_t.Init(2,10,0);
	var que1 := new Queue.Init();
	assert pcb1.pid == 1;
	assert pcb1.duration == 10;
	assert pcb1.ownerID == 0;
	que1.enQueue(pcb1);que1.enQueue(pcb3);
	assert que1.que[0]== pcb1;
	var pcb2 :=que1.deQueue(); 
	assert pcb1.getPid()==pcb2.getPid();
	
}