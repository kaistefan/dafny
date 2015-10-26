class Kunde {
	var id : int;
	var value : int;
	constructor Init (i: int, v: int)
	modifies this;
	ensures getId() == i;
	ensures getValue() == v;
	{
		id, value := i, v;
	}
	function method getId () : int
	reads this;
	{
		id
	}
	function method getValue () : int
	reads this;
	{
		value
	}
}


class KundenDB{
	var db : seq<Kunde>;
	
	predicate Valid()
	reads this;
	reads db;
	{
		null !in db &&(forall i,j :: 0 <= i < j < |db| ==> db[i].getId() != db[j].getId())
	}

	predicate inDB(kid: int)
	requires Valid();
	reads this;
	reads db;
	{
		exists k: Kunde :: k in db && k.getId() == kid
	}

	method neuKunde (kid: int, v: int)
	requires Valid();
	modifies this;
	ensures Valid();
	ensures inDB(kid);
	{
		var i :=0;
		var drin :=false;
		while (i<|db|)
		invariant 0 <= i <= |db|;
		invariant Valid();
		invariant drin == true <==> exists k : Kunde :: k in db[..i] && k.getId() ==kid;
		{
			
			if (db[i].getId()==kid){
				drin:=true;
			}
			i:=1+i;
		}
		if(drin ==false)
		{
		    var kunde := new  Kunde.Init(kid,v);
			db:= db+[kunde];
		}
	}
	method updateKunde (kid: int, v: int)
	requires Valid();
	requires inDB(kid);
	requires |db|>0;
	modifies db;
	ensures Valid();
	ensures inDB(kid);
	{
		var kunde:Kunde ;
		var i :=0;
		ghost var index:=-1;
		while (i<|db|)
		invariant 0 <= i <= |db|;		
		invariant Valid();
		invariant inDB(kid);
		//invariant -1 <= index < |db|;
		//invariant -1<index==> db[index].getId()==kid && db[index].getValue()==v;
		//invariant  index >-1 ==> exists k : Kunde :: k in db[..i] && k.getId() ==kid;

		{
			if (db[i].getId() ==kid ){
				index:=i;
				kunde:= db[i];
				kunde.value:=v;
			}
			i:=i+1;
		}
	}
}