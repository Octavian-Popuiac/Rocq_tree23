Import Nat.

(* 2-3 Tree Implementation *)
Inductive tree23: Type :=
  | Leaf: tree23
  | Node2: tree23 -> nat -> tree23 -> tree23
  | Node3: tree23 -> nat -> tree23 -> nat -> tree23 -> tree23.

Inductive insert_result: Type :=
  | Done (t: tree23)
  | Split (l: tree23) (n: nat) (r: tree23).

Inductive delete_result: Type :=
  | Ok(t: tree23)
  | Underflow (t: tree23).

Fixpoint find_min (t: tree23): option nat :=
  match t with
  | Leaf => None
  | Node2 Leaf v _ => Some v
  | Node2 l _ _ => find_min l
  | Node3 Leaf v1 _ _ _ => Some v1
  | Node3 l _ _ _ _ => find_min l
  end.

Fixpoint remove_min (t: tree23) : (nat * delete_result) :=
  match t with
  | Leaf => (0, Underflow (Leaf)) (* nunca deve chegar aqui *)
  | Node2 Leaf v Leaf => (v, Underflow Leaf)
  | Node3 Leaf v1 Leaf v2 Leaf => (v1, Ok (Node2 Leaf v2 Leaf))
  | Node2 l v r =>
    let (m, res) := remove_min l in
    match res with
    | Ok l' => (m, Ok (Node2 l' v r))
    | Underflow l' =>
      match r with
      | Node3 rl rv1 rm rv2 rr => (m, Ok (Node2 (Node2 l' v rl) rv1 (Node2 rm rv2 rr)))
      | Node2 rl rv rr => (m, Underflow (Node3 l' v rl rv rr))
      | _ => (m, Underflow (Node2 l' v r))
      end
    end
  | Node3 l v1 m v2 r =>
    let (minv, res) := remove_min l in
    match res with
    | Ok l' => (minv, Ok (Node3 l' v1 m v2 r))
    | Underflow l' =>
      match m with
      | Node3 ml mv1 mm mv2 mr => (minv, Ok (Node3 (Node2 l' v1 ml) mv1 (Node2 mm mv2 mr) v2 r))
      | Node2 ml mv mr => (minv, Ok (Node2 (Node3 l' v1 ml mv mr) v2 r))
      | _ => (minv, Underflow (Node3 l' v1 m v2 r))
      end
    end
  end.

(* Search for a value in the 2-3 tree *)
Fixpoint search (n: nat) (t: tree23): bool :=
  match t with
  | Leaf => false
  | Node2 l v r =>
    if ltb n v then search n l
    else if ltb v n then search n r
    else true
  | Node3 l v1 m v2 r =>
    if eqb n v1 then true
    else if ltb n v1 then search n l
    else if ltb n v2 then search n m
    else if ltb v2 n then search n r
    else true
  end.

Compute Node3 Leaf 10 Leaf 20 Leaf.
Compute search 15 (Node3 Leaf 15 Leaf 20 Leaf).
(* true *)
Compute search 20 (Node3 Leaf 10 Leaf 20 Leaf).
(* true *)
Compute search 7 (Node3 Leaf 10 Leaf 20 Leaf).
(* false *)

(* Insert a value into the 2-3 tree *)
Fixpoint insert_helper (n: nat) (t: tree23): insert_result :=
  match t with
  | Leaf => Done (Node2 Leaf n Leaf)
  | Node2 l v r =>
    if ltb n v then
      match l with
      | Leaf => Done (Node3 Leaf n Leaf v r)
      | _ =>
        match insert_helper n l with
        | Done l' => Done (Node2 l' v r)
        | Split l1 x l2 => Done (Node3 l1 x l2 v r)
        end
      end
    else if ltb v n then
      match r with
      | Leaf => Done (Node3 l v Leaf n Leaf)
      | _ =>
        match insert_helper n r with
        | Done r' => Done (Node2 l v r')
        | Split r1 x r2 => Done (Node3 l v r1 x r2)
        end
      end
    else
      Done t

  | Node3 l v1 m v2 r =>
    if eqb n v1 then Done t
    else if eqb n v2 then Done t

    (* Esquerda *)
    else if ltb n v1 then
      match l with
      | Leaf => Split (Node2 Leaf n Leaf) v1 (Node2 m v2 r)
      | _ => 
        match insert_helper n l with
        | Done l' => Done (Node3 l' v1 m v2 r)
        | Split l1 x l2 => Split (Node2 l1 x l2) v1 (Node2 m v2 r)
        end
      end
    
    (* Meio *)
    else if ltb n v2 then
      match m with
      | Leaf => Split (Node2 l v1 Leaf) n (Node2 Leaf v2 r)
      | _ => 
        match insert_helper n m with
        | Done m' => Done (Node3 l v1 m' v2 r)
        | Split m1 x m2 => Split (Node2 l v1 m1) x (Node2 m2 v2 r)
        end
      end
    
    (* Direita *)
    else
      match r with
      | Leaf => Split (Node2 l v1 m) v2 (Node2 Leaf n Leaf)
      | _ =>
        match insert_helper n r with
        | Done r' => Done (Node3 l v1 m v2 r')
        | Split r1 x r2 => Split (Node2 l v1 m) v2 (Node2 r1 x r2)
        end
      end
  end.

Definition insert (n: nat) (t: tree23): tree23 :=
  match insert_helper n t with
  | Done t' => t'
  | Split l x r => Node2 l x r (* nova raiz se a antiga arrebentou *)
  end.

(* Testar Inserts *)
Compute insert 10 Leaf.
(* Esperado: Node2 Leaf 10 Leaf *)
Compute insert 5 (Node2 Leaf 10 Leaf).
(* Esperado: Node3 Leaf 5 Leaf 10 Leaf *)
Compute insert 15 (Node2 Leaf 10 Leaf).
(* Esperado: Node3 Leaf 10 Leaf 15 Leaf *)

Definition tree_1 := Node3 Leaf 10 Leaf 20 Leaf.
Compute insert 15 tree_1.
(* Esperado: Node2 (Node2 Leaf 10 Leaf) 15 (Node2 Leaf 20 Leaf) *)
Compute insert 5 tree_1.
(* Esperado: Node2 (Node2 Leaf 5 Leaf) 10 (Node2 Leaf 20 Leaf) *)
Compute insert 25 tree_1.
(* Esperado: Node2 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 25 Lead) *)

Definition tree_2 := Leaf.
Compute insert 10 tree_2.
(* Esperado: Node2 Leaf 10 Leaf *)
Compute insert 20 (insert 10 tree_2).
(* Esperado: Node3 Leaf 10 Leaf 20 Leaf *)
Compute insert 30 (insert 20 (insert 10 tree_2)).
(* Esperado: Node2 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf) *)
Compute insert 40 (insert 30 (insert 20 (insert 10 tree_2))).
(* Esperado: Node2 (Node2 Leaf 10 Leaf) 20 (Node3 Leaf 30 Leaf 40 Leaf) *)
Compute insert 50 (insert 40 (insert 30 (insert 20 (insert 10 tree_2)))).
(* Esperado: Node3 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf) 40 (Node2 Leaf 50 Leaf)*)
Compute insert 60 (insert 50 (insert 40 (insert 30 (insert 20 (insert 10 tree_2))))).
(* Esperado: Node3 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf) 40 (Node3 Leaf 50 Leaf 60 Leaf) *)
Compute insert 70 (insert 60 (insert 50 (insert 40 (insert 30 (insert 20 (insert 10 tree_2)))))).
(* Esperado: Node2 (Node2 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf)) 40 (Node2 (Node2 Leaf 50 Leaf) 60 (Node2 Leaf 70 Leaf)) *)

Definition t0 := Leaf.
Definition t1 := insert 30 t0.
Definition t2 := insert 20 t1.
Definition t3 := insert 40 t2.
Definition t4 := insert 25 t3.
Definition t5 := insert 10 t4.
Definition t6 := insert 50 t5.
Definition t7 := insert 5 t6.
Definition t8 := insert 60 t7.
Compute t8.
(* Esperado: Node2 (Node2 (Node3 Leaf 5 Leaf 10 Leaf) 20 (Node2 Leaf 25 Leaf) 30 (Node2 (Node2 Leaf 40 Leaf) 50 (Node2 Leaf 60 Leaf))) *)

(* Delete a value from the 2-3 tree *)
Fixpoint delete_helper (n: nat) (t: tree23): delete_result :=
  match t with
  | Leaf => Ok Leaf

  | Node2 l v r => 
    if ltb n v then
      match delete_helper n l with
      | Ok l' => Ok (Node2 l' v r)
      | Underflow l' =>
        match r with
        (* Borrow *)
        | Node3 rl rv1 rm rv2 rr =>
          Ok (Node2 (Node2 l' v rl) rv1 (Node2 rm rv2 rr))
        (* Merge *)
        | Node2 rl rv rr =>
          Underflow (Node3 l' v rl rv rr)
        | _ => Underflow (Node2 l' v r)
        end
      end
    else if ltb v n then
      match delete_helper n r with
      | Ok r' => Ok (Node2 l v r')
      | Underflow r' =>
        match l with
        (* Borrow *)
        | Node3 ll lv1 lm lv2 lr =>
          Ok (Node2 (Node2 ll lv1 lm) lv2 (Node2 lr v r'))
        (* Merge *)
        | Node2 ll lv lr =>
          Underflow (Node3 ll lv lr v r')
        | _ => Underflow (Node2 l v r')
        end
      end
    else
      match r with
      | Leaf => Underflow Leaf
      | _ =>
        let (m, res) := remove_min r in
        match res with
        | Ok r' => Ok (Node2 l m r')
        | Underflow r' =>
          match l with
          | Node3 ll lv1 lm lv2 lr => Ok (Node2 (Node2 ll lv1 lm) lv2 (Node2 lr m r'))
          | Node2 ll lv lr => Underflow (Node3 ll lv lr m r')
          | _ => Underflow (Node2 l m r')
          end
        end
      end
  | Node3 l v1 m v2 r =>
    if eqb n v1 then
      match l, m, r with
      | Leaf, Leaf, Leaf => Ok (Node2 l v2 r)
      | _, _, _ =>
        let (x, res) := remove_min m in
        match res with
        | Ok m' => Ok (Node3 l x m' v2 r)
        | Underflow m' =>
          match l with
          | Node3 ll lv1 lm lv2 lr => Ok (Node3 (Node2 ll lv1 lm) lv2 (Node2 lr x m') v2 r)
          | Node2 ll lv lr => Ok (Node2 (Node3 ll lv lr x m') v2 r)
          | _ => Underflow (Node3 l x m' v2 r)
          end
        end
      end
    else if eqb n v2 then
      match l, m, r with
      | Leaf, Leaf, Leaf => Ok (Node2 l v1 m)
      | _, _, _ =>
        let (x, res) := remove_min m in
        match res with
        | Ok m' => Ok (Node3 l v1 m' x r)
        | Underflow m' =>
          match m with
          | Node3 ml mv1 mm mv2 mr => Ok (Node3 l v1 (Node2 ml mv1 mm) mv2 (Node2 mr x m'))
          | Node2 ml mv mr => Ok (Node2 l v1 (Node3 ml mv mr x m'))
          | _ => Underflow (Node3 l v1 m' x r)
          end
        end
      end
    else if ltb n v1 then
      match delete_helper n l with
      | Ok l' => Ok (Node3 l' v1 m v2 r)
      | Underflow l' =>
        match m with
        (* Borrow do meio *)
        | Node3 ml mv1 mm mv2 mr => Ok (Node3 (Node2 l' v1 ml) mv1 (Node2 mm mv2 mr) v2 r)
        (* Merge com meio *)
        | Node2 ml mv mr => Ok (Node2 (Node3 l' v1 ml mv mr) v2 r)
        | _ => Underflow (Node3 l' v1 m v2 r)
        end
      end
    else if ltb n v2 then
      match delete_helper n m with
      | Ok m' => Ok (Node3 l v1 m' v2 r)
      | Underflow m' =>
        match l, r with
        (* Borrow da esquerda *)
        | Node3 ll lv1 lm lv2 lr, _ => Ok (Node3 (Node2 ll lv1 lm) lv2 (Node2 lr v1 m') v2 r)
        (* Borrow da direita *)
        | _, Node3 rl rv1 rm rv2 rr => Ok (Node3 l v1 (Node2 m' v2 rl) rv1 (Node2 rm rv2 rr))
        (* Merge da esquerda *)
        | Node2 ll lv lr, _ => Ok (Node2 (Node3 ll lv lr v1 m') v2 r)
        (* Merge da direita *)
        | _, Node2 rl rv rr => Ok (Node2 l v1 (Node3 m' v2 rl rv rr))
        | _, _ => Underflow (Node3 l v1 m' v2 r)
        end
      end
    else
      match delete_helper n r with
      | Ok r' => Ok (Node3 l v1 m v2 r')
      | Underflow r' =>
        match m with
        (* Borrow do meio *)
        | Node3 ml mv1 mm mv2 mr => Ok (Node3 l v1 (Node2 ml mv1 mm) mv2 (Node2 mr v2 r'))
        (* Merge com meio *)
        | Node2 ml mv mr => Ok (Node2 l v1 (Node3 ml mv mr v2 r'))
        | _ => Underflow (Node3 l v1 m v2 r')
        end
      end
  end.

Definition delete (n: nat) (t: tree23): tree23 :=
  match delete_helper n t with
  | Ok t' => t'
  | Underflow t' => 
    match t' with
    | Node2 Leaf _ Leaf => Leaf
    | Node2 l _ r =>
      match l, r with
      | Leaf, _ => r
      | _, Leaf => l
      | _, _ => t'
      end
    | _ => t' (* não deveria acontecer *)
    end
  end.

Compute delete 10 (Node2 Leaf 10 Leaf).
(* Esperado: Leaf *)
Compute delete 5 (Node2 Leaf 10 Leaf).
(* Esperado: Node2 Leaf 10 Leaf *)
Compute delete 10 (Node3 Leaf 10 Leaf 20 Leaf).
(* Esperado: Node2 Leaf 20 Leaf *)
Compute delete 20 (Node3 Leaf 10 Leaf 20 Leaf).
(* Esperado: Node2 Leaf 10 Leaf *)
Compute delete 5 (Node3 Leaf 10 Leaf 20 Leaf).
(* Esperado: Node3 Leaf 10 Leaf 20 Leaf *)

Definition t_del_1 := Node2 (Node2 Leaf 10 Leaf) 20 (Node3 Leaf 30 Leaf 40 Leaf).
Compute delete 10 t_del_1.
(* Esperado: Node2 (Node2 Leaf 20 Leaf) 30 (Node2 Leaf 40 Leaf) *)
Definition t_del_2 := Node2 (Node3 Leaf 5 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf).
Compute delete_helper 30 t_del_2.
(* Esperado: Ok (Node2 (Node2 Leaf 5 Leaf) 10 (Node2 Leaf 20 Leaf)) *)

Definition t_del_3 := Node2 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf).
Compute delete 10 t_del_3.
(* Esperado: Node3 Leaf 20 Leaf 30 Leaf *)
Compute delete_helper 30 t_del_3.
(* Esperado: Underflow (Node3 Leaf 10 Leaf 20 Leaf) *)

Definition t_m1 := Node2 (Node2 Leaf 10 Leaf) 20 (Node2 Leaf 30 Leaf).
Compute delete 10 t_m1.
(* Esperado: Node3 Leaf 20 Leaf 30 Leaf *)
Compute delete 30 t_m1.
(* Esperado: Node3 Leaf 10 Leaf 20 Leaf *)

Definition t_p1 := Node2 (Node2 (Node2 Leaf 1 Leaf) 2 (Node2 Leaf 3 Leaf)) 10 (Node2 Leaf 20 Leaf).
Compute delete 1 t_p1.

Definition t_p2 := Node2 (Node2 (Node3 Leaf 18 Leaf 27 Leaf) 36 (Node2 Leaf 45 Leaf)) 54 (Node3 (Node2 Leaf 63 Leaf) 69 (Node3 Leaf 72 Leaf 81 Leaf) 90 (Node2 Leaf 99 Leaf)).
Definition t_del_69 := delete 69 t_p2.
Compute t_del_69.
Definition t_del_72 := delete 72 t_del_69.
Compute t_del_72.
Definition t_del_99 := delete 99 t_del_72.
Compute t_del_99.
Definition t_del_81 := delete 81 t_del_99.
Compute t_del_81.

