function Ackermann (m: nat, n : nat) : nat
decreases m,n;
{
	if m == 0 then
	n + 1
	else if n == 0 then
	Ackermann (m - 1, 1)
	else
	Ackermann (m - 1, Ackermann(m, n-1))
}

method Hoenicke(x: int, y: int)
{
	var m := x;
	var n := y;
	while (n > 0 && m < 100)
	decreases 100 - m;
	{
		m := m + n;
	}
}

method Find (a: array<int>, key: int) returns (index: int)
requires a != null;
ensures 0 <= index ==> index < a.Length && a[index] == key;
ensures index < 0 ==> forall k :: 0 <= k < a.Length
==> a[k] != key;
{
index := -1;
var i := 0;
while (i < a.Length)
invariant 0 <= i <= a.Length;
invariant 0 <= index ==>
index < a.Length && a[index] == key;
invariant index < 0 ==>
forall k :: 0 <= k < i ==> a[k] != key;
{
	if (a[i] == key) {
		index := i;
	}
	i:= i + 1;
}
}

method max (a: array<int>) returns (index:int)
requires a != null;
requires a.Length >0
{
	index :=0;
	var i :=0;
	while(i<a.Length)
	invariant 0 <= i <= a.Length;
	invariant 0 <= index < a.Length;
	
	{
		if(a[index]<a[i]){
		index :=i;
		}
		i:= i +1;
	}
}


function sorted (a: array<int>) : bool
requires a!= null;
reads a;
{
forall k,j :: 0 <= k < j < a.Length ==> a[k] <= a[j]
}

method smax (a: array<int>) returns (index:int)
requires a != null;
requires a.Length >0
{
	if(a.Length == 1 )
	{
		index:=0;
	}
	else{
		if ( a [0]>a[1]){
			index :=0;
		}
		else{
		index:= a.Length -1;
		}
	 }
}

function distinct (a: array<int>) : bool
requires a!= null;
reads a;
{
	forall k,j :: 0 <= k < j < a.Length ==> a[k] != a[j]
}

method addCustomer(a: array<int>, v: int) returns (r: array<int>)
requires a != null;
requires distinct(a);
ensures r != null;
ensures distinct(r);
ensures exists i :: 0 <= i < r.Length && r[i] == v;
{
	var i:=0;
	if (a.Length ==0){
	 r:= new int [1];
	 r[0]:=v;
	}
	else{
		if (!exists i :: 0 <= i < a.Length && a[i] == v)
		{
			r :=  new int[a.Length+1];
			i:=0;
			while (i<a.Length)
			invariant 0 <= i <= a.Length;
			invariant forall j :: 0 <=j <i  ==> r[j]==a[j];
			{
				r[i]:=a[i];
				i:=i+1;
			}
			r[r.Length-1]:=v;
		}
		else{
			r:=a;
		}
	}
}