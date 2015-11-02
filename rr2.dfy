/* Process Control Block */
class PCB_t {
	var pid : int;
	var duration : int;
	var ownerID :int;
	var usedCPU : int;
	constructor Init (a: int, b: int, c: int)
	modifies this;
	ensures getPid() == a;
	ensures getDuration() == b;
	ensures getOwnerID() == c;
	ensures usedCPU == 0;
	{
		pid, duration, ownerID := a, b, c;
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
/* Operating System */
class OS {
	var que : seq<PCB_t>;
	var pcb : PCB_t;
	var quantum : int;

	predicate Valid()
	reads this;
	reads que;
	{
		null !in que && (forall i,j :: 0 <= i < j < |que| ==> que[i].getPid() != que[j].getPid())
	}
	predicate inQue(pid: int)
	requires Valid();
	reads this;
	reads que;
	ensures Valid();
	{
		exists k: PCB_t :: k in que && k.getPid() == pid
	}


	constructor Init(a: int)
	modifies this;
	ensures quantum == a;
	ensures pcb == null;
	ensures que == [];
	ensures Valid();
	{
		pcb := null;
		quantum := a;
		que := [];
	}

	method enQueue (a: PCB_t) 
	requires Valid();
	requires a!=null;
	requires |que| >= 0;
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

	method deQueue ()  returns (a: PCB_t)
	requires Valid();
	requires |que|>0;
	modifies this;
	ensures Valid();
	ensures a == old(que[0]);
	ensures |que| == old(|que|)-1;
	ensures  que== old (que[1..]);
	ensures a == pcb;
	ensures |que| >= 0;
	{ 
		pcb := que[0];
		a := pcb; 
		que := que[1..];  
	}
	/*
	method getPCB() returns (a: PCB_t)
	requires que != null;
	requires pcb == null;
	requires Valid();
	requires |que| > 0;
	modifies this;
	modifies que;
	ensures a == pcb;
	ensures que != null;
	ensures Valid();
	
	{
		pcb := deQueue();
		a := pcb;
	}
	*/
	method operate()
	requires pcb != null;
	requires Valid();
	requires |que| > 0;
	requires !inQue(pcb.getPid());
	modifies this;
	modifies que;
	modifies pcb;
	ensures pcb == null;
	ensures old (pcb.usedCPU + quantum < pcb.duration) ==> |que| > 0 && Valid() && inQue(old(pcb.getPid()));
	ensures |que| >= 0;
	ensures Valid();
	{
		pcb.usedCPU := pcb.usedCPU + quantum;
		if(pcb.usedCPU < pcb.duration) {
			enQueue(pcb);
			//assert inQue(pcb.getPid());
		}
		pcb := null;
	}
}

method main () 
{
    var pcb1 := new PCB_t.Init(1,80,5);
	var pcb2 := new PCB_t.Init(2,20,0);
	/*var pcb3 := new PCB_t.Init(3,90,0);
	var pcb4 := new PCB_t.Init(4,50,0);
	var pcb5 := new PCB_t.Init(5,10,0);
	var pcb6 := new PCB_t.Init(6,75,0);*/
	assert pcb1 != null;
	assert pcb1.pid == 1;
	assert pcb1.duration == 80;
	assert pcb1.ownerID == 5;
	assert pcb1 != pcb2;
	var os := new OS.Init(10);
	assert os != null;
	assert os.quantum == 10;
	assert os.pcb == null;
	assert |os.que| >= 0;
	assert null !in os.que;
	os.enQueue(pcb1);
	os.enQueue(pcb2);
	assert os.que[0] == pcb1;
	assert os.que[1] == pcb2;
	assert |os.que| == 2;
	var pcb3 := os.deQueue();
	assert pcb1 == pcb3;
	assert |os.que| == 1;
	assert pcb1.getPid() == pcb3.getPid();
	assert os.que[0] == pcb2;
	assert os.pcb != null;
	assert os.pcb == pcb3;
	os.operate();
	assert os != null;
	assert os.que[0] == pcb2;
	//assert os.que[0] == pcb2;
	/*var que1 := new Queue.Init();
	assert pcb1.pid == 1;
	assert pcb1.duration == 80;
	assert pcb1.ownerID == 5;
	que1.enQueue(pcb1);
	que1.enQueue(pcb3);
	assert que1.que[0] == pcb1;
	assert que1.que[1] == pcb3;
	assert |que1.que| == 2;
	var pcb2 := que1.deQueue();
	assert |que1.que| == 1;
	assert pcb1.getPid() == pcb2.getPid();*/
	
}