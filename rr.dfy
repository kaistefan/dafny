
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
	{
		pid, duration,ownerID := a,b,c;
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