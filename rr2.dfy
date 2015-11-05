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
	ensures que == [];
	ensures Valid();
	{
		quantum := a;
		que := [];
	}

	method enQueue (a: PCB_t) 
	requires Valid();
	requires a!=null;
	requires |que| >= 0;
	requires !inQue(a.getPid());
	modifies this`que;
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
	modifies this`que;
	ensures Valid();
	ensures a == old(que[0]);
	ensures |que| == old(|que|)-1;
	ensures  que== old (que[1..]);
	ensures |que| >= 0;
	{ 
		
		a := que[0]; 
		que := que[1..];  
	}
	

	method operate()
	requires Valid();
	requires |que| > 0;
	modifies this`que;
	modifies que[0];
	ensures Valid();
	ensures old (que[0].usedCPU + quantum < que[0].duration) ==> |que| == old(|que|) && Valid() && inQue(old(que[0].getPid()))&& exists pcb: PCB_t:: (pcb != null && pcb==old(que[0]) && que==old(que[1..]+[pcb]));
	ensures old (que[0].usedCPU + quantum >= que[0].duration) ==> |que|+1 == old(|que|) && Valid() && !inQue(old(que[0].getPid()))&& que==old(que[1..]);
	
	{
		ghost var qsize := |que|;
		ghost var head := que[0];
		var pcb := deQueue();
		assert pcb == head;
		assert qsize == |que| + 1;
		pcb.usedCPU := pcb.usedCPU + quantum;
		assert pcb == old(que[0]);
		assert pcb.usedCPU == old (que[0].usedCPU + quantum);
		
		print("pid: ");print(pcb.pid);print(" | duration: ");print(pcb.duration);print(" | usedCPU: ");print(pcb.usedCPU);

		if(pcb.usedCPU < pcb.duration) {
			enQueue(pcb);
			assert qsize == |que|;
			assert  old (que[0].usedCPU + quantum < que[0].duration) ==> |que| == old(|que|);
			print(" | wird eingereit \n");
		} else {
			print(" | wird nicht eingereit \n");
		}
		assert  old (que[0].usedCPU + quantum < que[0].duration) ==> |que| == old(|que|);



		pcb := null;
	}
}

method Main () 
{
    var pcb1 := new PCB_t.Init(1,80,5);
	var pcb2 := new PCB_t.Init(2,20,0);
	var pcb3 := new PCB_t.Init(3,90,0);
	var pcb4 := new PCB_t.Init(4,50,0);
	var pcb5 := new PCB_t.Init(5,10,0);
	var pcb6 := new PCB_t.Init(6,75,0);
	assert pcb1 != null;
	assert pcb1.pid == 1;
	assert pcb1.duration == 80;
	assert pcb1.ownerID == 5;
	assert pcb1 != pcb2;
	var os := new OS.Init(10);
	assert os != null;
	assert os.quantum == 10;	
	assert |os.que| >= 0;
	assert null !in os.que;
	os.enQueue(pcb1);
	os.enQueue(pcb2);
	assert os.que[0] == pcb1;
	assert os.que[1] == pcb2;
	assert |os.que| == 2;
	os.enQueue(pcb3);
	os.enQueue(pcb4);
	os.enQueue(pcb5);
	os.enQueue(pcb6);
	var i :=0;
	while (i<34&&|os.que|>0)
	invariant    0 <= i <= 34;
	invariant os.Valid();
	invariant fresh (os);
	invariant fresh (os.que);
	{
	os.operate();
	i:=i+1;
	}
}