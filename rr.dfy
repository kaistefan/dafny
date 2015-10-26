
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
class Node {
	var data: PCB_t;
	var next: Node;

	method Init()
    modifies this;
    ensures next == null;
	ensures this != null; 
	{
		 next := null;
	}
}

class Queue  {
	var head : Node;
	var tail : Node;
	predicate Valid()
	reads this;
	reads tail;
	{
		(head == null <==> tail ==null) || (head!=null <==> tail!=null  )
	}
	/*predicate inDB(a: PCB_t)
	requires Valid();
	requires a!=null;
	reads a;
	reads this;
	{
		
	}*/
	constructor Init ()
	modifies this;
	ensures Valid();
	{
		tail,head:=null,null;
	}

	method enQueue (a:PCB_t) 
	requires Valid();
	requires a!=null;
	modifies this;
	modifies tail
	ensures Valid();
	ensures tail.next ==null;
	{
		if(head==null)
		{
			head := new Node.Init();
			head.data:=a;
			tail:=head;
		}
		else{
		tail.next:= new Node.Init();
		tail.next.data:=a;
		tail:=tail.next;
		}
	}

	method deQueue ()  returns (a:PCB_t)
	requires Valid();
	modifies this;
	ensures Valid();
	{    
	}
	
}

method main () {
	var pcb1 := new PCB_t.Init(1,10,0);
	assert pcb1.pid == 1;
	assert pcb1.duration == 10;
	assert pcb1.ownerID == 0;
}