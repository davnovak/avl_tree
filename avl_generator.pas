{ Implementace AVL-stromu }
{ David Novak, ZS 2017-2018 }
{ Programovani I, NPRG030 }
{# # # # # # # # # # # # # #}
{Pascal implementation of AVL-trees (self-balancing binary trees) for storing 32-bit integer values.}
program Avl_generator; uses Crt;

{Define type for node of tree and for pointer to the node.}
type p_Avl = ^Avl_node;
 Avl_node = record
 key: integer; {Key is the integer value we want to store.}
 l, r, par: p_Avl; {Pointers to the left child of node, right child of node and parent of node.}
 bal, h: integer; {Balance factor and height factor.}
 end;

procedure init(var root: p_Avl); begin new(root); root:=nil end; {Initialise an empty root.}

function get_path(var root: p_Avl; what: integer): string; {Retrieve a path from root to node of key 'what'.}
  {At each decision point, if target value is less than key of current node, go to its left child, vice versa.}
var found: boolean;
    report, newb: string;
    tmp: p_Avl;
begin
  found:=false; report:=''; tmp:=root;
  while((tmp<>nil) and (not found)) do
  begin
    str(tmp^.key, newb); report:=report+newb+' -> ';
    if(tmp^.key=what) then found:=true
      else if(tmp^.key>what) then tmp:=tmp^.l
      else tmp:=tmp^.r;
  end;
  if(report<>'') then report:=copy(report,1,length(report)-4);
  if found then get_path:=report else get_path:='Node not found.';
end; {get_path}

function get_min(var root: p_Avl): string; {Retrieve a path to node of lowest value of key.}
  {Similar to get_path, but always go left, to eventually reach the minimum value.}
var report, newb: string;
    tmp: p_Avl;
begin
  if(root=nil) then begin writeln('Tree empty.'); exit; end;
  report:=''; tmp:=root;
  while(tmp<>nil) do
  begin
    str(tmp^.key, newb); report:=report+newb+' -> ';
    tmp:=tmp^.l;
  end;
  if(report<>'') then report:=copy(report,1,length(report)-4);
  get_min:=report;
end; {get_min}

function get_max(var root: p_Avl): string; {Retrieve a path to node of highest value of key.}
  {Similar to get_path, but always go right, to eventually reach the maximum value.}
var report, newb: string;
    tmp: p_Avl;
begin
  if(root=nil) then begin writeln('Tree empty.'); exit; end;
  report:=''; tmp:=root;
  while(tmp<>nil) do
  begin
    str(tmp^.key, newb); report:=report+newb+' -> ';
    tmp:=tmp^.r;
  end;
  if(report<>'') then report:=copy(report,1,length(report)-4);
  get_max:=report;
end; {get_max}

function get_height(var n: p_Avl): integer; {Retrieve height of node: if we're looking at NIL, the
retrieved value MUST be smaller than when looking at a childless node, hence return -1 in that case.}
begin if(n=nil) then get_height:=-1 else get_height:=n^.h; end;

procedure reheight(var n: p_Avl); {Refresh height factor of node.}
  {Do this by taking the larger of children's height factors and increment it (because we're looking at
  a level above the children).}
begin
  if(n<>nil) then
    if(get_height(n^.r)>get_height(n^.l)) then n^.h:=1+get_height(n^.r)
      else n^.h:=1+get_height(n^.l);
end; {reheight}

procedure set_balance(var n: p_Avl); begin reheight(n); n^.bal:=get_height(n^.r)-get_height(n^.l); end;
{^ Refresh balance factor of node.}

function rotate_l(a: p_Avl): p_Avl; {Conduct a left rotation on a subtree, with pivot 'a',
return new root to subtree. See external documentation for details.}
var b: p_Avl;
begin
  b := a^.r;
  b^.par := a^.par;
  a^.r := b^.l;
  if(a^.r<>nil) then a^.r^.par := a;
  b^.l := a;
  a^.par := b;
  if(b^.par<>nil) then
    if(b^.par^.r=a) then b^.par^.r := b
      else b^.par^.l := b;
  set_balance(a); set_balance(b);
  rotate_l := b;
end; {rotate_l}

function rotate_r(a: p_Avl): p_Avl; {Conduct a right rotation on a subtree, with pivot 'a',
return new root to subtree. See external documentation for details.}
var b: p_Avl;
begin
  b := a^.l;
  b^.par := a^.par;
  a^.l := b^.r;
  if(a^.l<>nil) then a^.l^.par := a;
  b^.r := a;
  a^.par := b;
  if(b^.par<>nil) then
    if(b^.par^.r=a) then b^.par^.r := b
      else b^.par^.l := b;
  set_balance(a); set_balance(b);
  rotate_r := b;
end; {rotate_r}

function rotate_l_r(a: p_Avl): p_Avl; {Conduct a left-right rotation on a subtree,
with pivot 'a', return new root to subtree. See external documentation for details.}
begin
  a^.l := rotate_l(a^.l);
  rotate_l_r := rotate_r(a);
end; {rotate_l_r}

function rotate_r_l(a: p_Avl): p_Avl; {Conduct a right-left rotation on a subtree,
with pivot 'a', return new root to subtree. See external documentation for details.}
begin
  a^.r := rotate_r(a^.r);
  rotate_r_l := rotate_l(a);
end; {rotate_r_l}

procedure rebalance(var root: p_Avl; n: p_Avl); {Look at a subtree with root 'n', adjust
height and balance factors and decide whether rotation is necessary.}
begin
  set_balance(n); {Refresh balance and height factors.}
  if(n^.bal=-2) then {If subtree is left-unbalanced...}
  begin
    if(get_height(n^.l^.l)>=get_height(n^.l^.r)) then n:=rotate_r(n) {...if it is left-left-unbalanced,
    then do a simple right-rotation.}
      else n:=rotate_l_r(n); {else, if it is left-right-unbalanced, do a right-left-rotation.}
  end
  else if(n^.bal=2) then {If subtree is right-unbalanced...}
  begin
    if(get_height(n^.r^.r)>=get_height(n^.r^.l)) then n:=rotate_l(n) {...if it is right-right-unbalanced,
    then do a simple left-rotation.}
      else n:=rotate_r_l(n); {...if it is right-left-unbalanced, do a right-left-rotation.}
  end;
  if(n^.par<>nil) then rebalance(root, n^.par) else root:=n; {Progress through parental lineage
  and keep rebalancing until we reach the root. Recursive calling of 'rebalance'.}
end; {rebalance}

procedure insert(var root: p_Avl; what: integer); {Insert a new node of key 'what' to tree of root 'root'.}
  {We must respect the rules of binary trees: lower key value in left child, higher key value in right child.}
var found: boolean;
  pre_tmp, tmp: p_Avl;
begin
  found:=false; tmp:=root; pre_tmp:= nil;
  while(tmp<>nil) and not found do
    if(tmp^.key=what) then found:=true
      else if(tmp^.key>what) then begin pre_tmp:=tmp; tmp:=tmp^.l end
      else begin pre_tmp:=tmp; tmp:=tmp^.r end;
  if not found then
  begin
    new(tmp); tmp^.key:=what;
    tmp^.l:=nil; tmp^.r:=nil; tmp^.par:=pre_tmp; tmp^.h:=0; tmp^.bal:=0;
    if(pre_tmp=nil) then root:=tmp
      else
      begin
        if(pre_tmp^.key>what) then pre_tmp^.l:=tmp else pre_tmp^.r:=tmp;
        rebalance(root, pre_tmp);
      end;
  end;
end; {insert}

procedure delete(var root: p_Avl; what: integer); {Delete a node of key 'what' from tree of root 'root'.}
  {We have to do some rewiring, unless the deleted node is the last child.}
var found: boolean;
  tmp, pre_tmp, act, pre_act: p_Avl;
begin
  found:=false; tmp:=root; pre_tmp:=nil;
  while(tmp<>nil) and not found do
  begin
    if(tmp^.key=what) then found:=true
      else if(tmp^.key>what) then
        begin pre_tmp:=tmp; tmp:=tmp^.l end
      else
        begin pre_tmp:=tmp; tmp:=tmp^.r end;
    if found then
      if(tmp^.l=nil) then
      begin
        if(pre_tmp=nil) then begin root:=tmp^.r; dispose(tmp); end
          else if(pre_tmp^.key>what) then begin pre_tmp^.l:=tmp^.r; dispose(tmp); rebalance(root,pre_tmp); end
          else begin pre_tmp^.r:=tmp^.r; dispose(tmp); rebalance(root,pre_tmp); end
      end else if(tmp^.r=nil) then
      begin
        if(pre_tmp=nil) then begin root:=tmp^.l; dispose(tmp); end
          else if(pre_tmp^.key>what) then begin pre_tmp^.l:=tmp^.l; dispose(tmp); rebalance(root,pre_tmp); end
          else begin pre_tmp^.r:=tmp^.l; dispose(tmp); rebalance(root,pre_tmp); end;
      end else
      begin {If the node we're deleting has two children, we'll have to find the rightmost node of its left subtree,
      move its key into the orginal node and delete this newly identified node.}
        act:=tmp^.l; pre_act:=nil;
        while(act^.r<>nil) do begin pre_act:=act; act:=act^.r end;
        tmp^.key:=act^.key;
        if(pre_act=nil) then begin tmp^.l:=act^.l; dispose(act); rebalance(root,tmp) end
          else begin pre_act^.r:=act^.l; dispose(act); rebalance(root,pre_act) end;
        {The 'rebalance' procedure is called whenever we're deleting a node different than root of tree.}
      end;
  end;
end; {delete}

function to_val(what: string): integer; {Convert string to integer using Horener's scheme.}
var ind, output, asc: integer;
begin
   ind:=1; output:=0;
   asc:=ord(what[ind]);
   while(asc>47) and (asc<58) do
   begin
      output:=output*10+(asc-48);
      inc(ind); asc:=ord(what[ind]);
   end;
   to_val:=output;
end; {to_val}

procedure interpret(var root: p_Avl; what: string); {Interpret user's input.}
var keyw, param, output: string;
  space, param_val: integer;
begin
	if(what='find min') then begin output:=get_min(root); writeln(output) end
	else if(what='find max') then begin output:=get_max(root); writeln(output) end
	else
	begin
		space:=1; while((what[space]<>' ') and (space<length(what))) do inc(space);
		if(space=length(what)) then exit;
		keyw:=copy(what,1,space-1); param:=copy(what,space+1,length(what)-space);
		param_val:=to_val(param);
		if(keyw='ins') then insert(root, param_val)
		  else if(keyw='del') then delete(root, param_val)
		  else if(keyw='find') then begin output:=get_path(root, param_val); writeln(output) end;
	end;
end; {interpret}

var Avl_tree: p_Avl;
  inp:string;
begin
  ClrScr;
  writeln('Avl_generator');
  init(Avl_tree);
  writeln('Initialised AVL tree. Use keywords "ins" and "del" with 32-bit integers.');
  writeln('Use "find" with integer of "min", "max", "all".');
  writeln('Enter "q" to quit the program.');
  readln(inp);
  while(inp<>'q') do
  begin
    interpret(Avl_tree, inp); readln(inp);
  end;
end.
