type 'a ab = Leaf | Node of registo
and registo = {mutable esq: int ab;  value : int ; mutable dir : int ab; mutable up : int ab; mutable pathParent : int ab}

(*Funções auxiliares*)

let rec insert_element ab x p pp =
  match ab with
  | Leaf -> Node {esq = Leaf; dir = Leaf; value = x; up = p; pathParent = pp}
  | Node s -> 
    if s.value > x
    then (s.esq <- insert_element s.esq x ab pp; ab)
    else (s.dir <- insert_element s.dir x ab pp; ab)

let changeParent p fNovo fAntigo =
  match p with 
  | Leaf -> ()
  | Node pai -> if pai.esq == fAntigo then pai.esq <- fNovo else pai.dir <- fNovo  
;;

let rotateRight ab =
  match ab with
  | Leaf -> ab
  | Node node -> 
    let nodeEsq = node.esq in 
    let pai = node.up in
    match nodeEsq with
    | Leaf -> ab (* nao e possivel fazer rotacao *)
    | Node nodeEsqConvertido ->
        nodeEsqConvertido.pathParent <- node.pathParent;
        node.pathParent <- Leaf;
        node.esq <- nodeEsqConvertido.dir; (* node.esq passou a ser nodoEsqDir *) 
        nodeEsqConvertido.up <- node.up; 
        node.up <- nodeEsq;
        nodeEsqConvertido.dir <- ab;
        match node.esq with 
        | Leaf -> changeParent pai nodeEsq ab; nodeEsq(* se for NULL nd a fazer*)
        | Node nodeEsqDirConvertido -> changeParent pai nodeEsq ab; nodeEsqDirConvertido.up <- ab; nodeEsq (* uso node.esq = nodoEsqDir, ver se nodeEsqDir diff de NULL *) 
;;

let rotateLeft ab =
  match ab with
  | Leaf -> ab
  | Node node -> 
    let nodeDir = node.dir in 
    let pai = node.up in
    match nodeDir with
    | Leaf -> ab (* nao e possivel fazer rotacao *)
    | Node nodeDirConvertido ->
        nodeDirConvertido.pathParent <- node.pathParent;
        node.pathParent <- Leaf;
        node.dir <- nodeDirConvertido.esq; (* node.dir passou a ser nodoDirEsq *) 
        nodeDirConvertido.up <- node.up; 
        node.up <- nodeDir;
        nodeDirConvertido.esq <- ab;
        match node.dir with 
        | Leaf -> changeParent pai nodeDir ab; nodeDir  (* se for NULL nd a fazer*)
        | Node nodeDirEsqConvertido -> changeParent pai nodeDir ab; nodeDirEsqConvertido.up <- ab; nodeDir (* uso node.dir = nodoDirEsq, ver se nodeDirEsq diff de NULL *) 
;;

let rec splay ab =
  match ab with
  | Leaf -> ab
  | Node node ->
    match node.up with
    | Leaf -> ab
    | Node paiNode -> 
      match paiNode.up with
      | Leaf -> if paiNode.esq == ab then rotateRight node.up else rotateLeft node.up (* comparar mesmo apontadores, com = da erro out_of_memory *)
      | Node avoNode ->
      if avoNode.esq == node.up && paiNode.esq == ab then splay (rotateRight (rotateRight paiNode.up)) (* Zig Zig esq*)
      else if avoNode.dir == node.up && paiNode.dir == ab then splay (rotateLeft (rotateLeft paiNode.up)) (* Zig Zig dir*)
      else if avoNode.dir == node.up && paiNode.esq == ab then (* Zig Zag dir esq a partir do avo*)
        let _ = rotateRight node.up in 
        splay (rotateLeft node.up)  
      else let _ = rotateLeft node.up in (* Zig Zag esq dir a partir do avo*)
        splay (rotateRight node.up)  
;;

let changeRightChild ab p =
  match ab with
  | Leaf -> ()
  | Node n -> n.up <- Leaf; n.pathParent <- p
;;

let rec access ab =
  let abNew = splay ab in
  match abNew with
  | Leaf -> abNew
  | Node node -> 
    let () = (changeRightChild node.dir abNew; node.dir <- Leaf) in
    if node.pathParent = Leaf then abNew
    else
        let paiNew = splay node.pathParent in
        match paiNew with
        | Leaf -> abNew
        | Node paiNode -> 
        let () = (changeRightChild paiNode.dir paiNew; paiNode.dir <- abNew; node.up <- paiNew; node.pathParent <- Leaf) in
        access abNew (* Irá fazer splay na nova chamada; Ate chegar a raiz de arvores de arvores*)
;;

(*********************)

(*Funções de linkagem*)

let linkAux nodeB a b =
  let _ = splay a in
  match a with
  | Leaf -> ()
  | Node nodeA -> nodeA.up <- b; nodeB.esq <- a   
;;

let rec swapChilds b =
  match b with
  | Leaf -> ()
  | Node n -> 
    let aux = n.dir in
    let () = n.dir <- n.esq in
    let () = n.esq <- aux in
    swapChilds n.esq; swapChilds n.dir 
;;

let link a b =
  let _ = access a in 
  let _ = access b in
  match b with
  | Leaf -> assert false
  | Node nodeB -> 
    match nodeB.esq with
    | Leaf -> linkAux nodeB a b; a
    | Node leftNode -> swapChilds b;
      let _ = splay a in
      match a with
      | Leaf -> assert false
      | Node nodeA -> nodeA.up <- b; nodeB.esq <- a; a
;;

(****************)

(*Funções de cut*)

let rec findElement a nodeB =
  match a with
  | Leaf -> false
  | Node nodeA -> if nodeA == nodeB then true else findElement nodeA.dir nodeB

let checkDeeper a b =
  let _ = access a in
  match a with
  | Leaf -> assert false
  | Node nodeA -> 
    match b with
    | Leaf -> assert false
    | Node nodeB -> if findElement nodeA.esq nodeB then a else b 
;;

let cut ab =
  let _ = access ab in
  match ab with
  | Leaf -> assert false
  | Node node -> 
    match node.esq with
    | Leaf -> ab 
    | Node leftNode -> leftNode.up <- Leaf; node.esq <- Leaf; ab
;;

(***************)

(*Função Link*)

let findRoot ab =
  let _ = access ab in
  match ab with
  | Leaf -> assert false  
  | Node n -> 
    let rec aux ar node =
      match node.esq with
      | Leaf -> access ar
      | Node leftNode -> aux node.esq leftNode
    in aux ab n
;;

(* Inicio de programa *)

let n,p = Scanf.sscanf (read_line ()) "%d %d" (fun x y -> (x,y))

let lista = Array.init (n+1) (fun i -> insert_element Leaf i Leaf Leaf)

let rec readInput i n =
  if i = n then () 
  else
    let ordem,a,b = Scanf.sscanf (read_line ()) "%s %d %d" (fun x y z -> (x,y,z)) in
    match ordem with
    | "ADD" -> let _ = link lista.(a) lista.(b) in readInput (i+1) n
    | "DEL" -> let _ = cut (checkDeeper lista.(a) lista.(b)) in readInput (i+1) n
    | "LINK" -> let x = findRoot(lista.(a)) and y = findRoot(lista.(b)) in
                if x == y then print_endline("YES") else print_endline("NO"); readInput (i+1) n
    | _ -> assert false
;;

let () = readInput 0 p