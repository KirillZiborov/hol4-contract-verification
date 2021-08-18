(* Type 'use "tools.sml";' to load these functions. *)

fun curry f x y = f (x, y);
fun uncurry f (x, y) = f x y;

fun fst (x,_) = x;
fun snd (_,y) = y;

fun whereIsStru struName = 
  let 
    val {allStruct=allstru, ...} = PolyML.globalNameSpace
    val sv = snd (Option.valOf (List.find (fn p => (fst p = struName)) (allstru ())))
    val ret = PolyML.NameSpace.Structures.properties sv
  in
    ret
    (* print (PolyML.makestring ret) *)
  end

fun whereIsVal valName = 
  let 
    val {allVal=allval, ...} = PolyML.globalNameSpace
    val sv = snd (Option.valOf (List.find (fn p => (fst p = valName)) (allval ())))
    val ret = PolyML.NameSpace.Values.properties sv
  in
    ret
    (*(PolyML.makestring ret) *)
  end

