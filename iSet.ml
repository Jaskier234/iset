(* autor: Artur Matyjasek *)
(* code review: Marcel Opiatowski *)

(* Przedział (a,b) lub None (używane w funkcji splt *)
type k = None | Some of int * int 

(* Drzewo AVL - 
  lewe poddrzewo 
  przedzial
  prawe poddrzewo
  wysokość
  sumaryczna długość przedziałów w poddrzewie (do below)
  zapisana w postaci max_int - s, żeby uniknąć problemów z przepełnieniem *)
type t =
  | Empty
  | Node of  t * k * t * int * int

let empty = Empty

let is_empty t = t = Empty

(* komparator 
  zwraca 0 gdy x i y mają niepustą część wspólną
  1/-1 gdy x i y są sąsiednimi przedziałami, np. [1,4] [5,7]
  2/-2 wpp, w zależności od tego, który przedział jest "większy"
  np. cmp [3,4] [-10,-8] = -2 *)
let rec cmp x y =
  match x, y with
  | Some(a, b), Some(c, d) -> 
    if a > c then -cmp (Some(c, d))  (Some(a, b))
    else if b >= c then 0
    else if b = c-1 then -1
    else -2
  | _ -> invalid_arg "cmp"

(* wysokość drzewa *)
let height t =
  match t with
  | Node(_, _, _, h, _) -> h
  | Empty -> 0

(* sumaryczna długość przedziałów drzewa *)
let size t =
  match t with
  | Node(_, _, _, _, s) -> s
  | Empty -> max_int (* max_int - 0  *)

(* długość przedziału [a,b] *)
let int_size a b =
  let l = max 0 (max_int - b + a) - 1 in
  max l 0

(* przyjmuje dwie liczby (max_int - x) (max_int - a)
  i zwraca (max_int - (x+y)) lub 0 gdy x+y przekroczyłoby max_int
  czyli gdy (max_int -(x+y)) < 0 *)
let dodaj a b =
  let l = a - (max_int - b) in
  max l 0 

(* zwraca drzewo, którego synami są l i r, a korzeniem k *)
let make l k r =
  match k with
  | Some(a, b) ->
    let s = dodaj (dodaj (size l) (size r)) (int_size a b) in
    Node (l, k, r, max (height l) (height r) + 1, s)
  | None -> invalid_arg "make"

(* zwraca zbalansowane (różnica wysokości < 3) drzewo *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else make l k r 

(* zwraca drzewo z dodanym przedziałem x. Zakładamy, że jeśli x = [a,b] to przedział [a-1,b+1] nie
  występuje w drzewie *)
let rec add_one x tree =
  if x = None then tree else 
  match tree with
  | Node (l, k, r, h, s) ->
      let c = cmp x k in
      if c = 0 then Node (l, x, r, h, s)(* nie powinno wystąpić *)
      else if c < 0 then
        let nl = add_one x l in
        bal nl k r
      else
        let nr = add_one x r in
        bal l k nr
  | Empty -> make Empty x Empty 

(* łączy 2 poddrzewa i element v *)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_one v r
  | (_, Empty) -> add_one v l
  | (Node(ll, lv, lr, lh, ls), Node(rl, rv, rr, rh, rs)) ->
    if lh > rh + 2 then bal ll lv (join lr v r) else
    if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

(* podobna do split ale zamiast boola zwraca znaleziony element lub None wpp,
  oraz przyjmuje funkcję st = w_przedziale x y *)      
let splt x tree st =
  let rec loop x = function
    | Empty -> (Empty, None, Empty)
    | Node (l, v, r, _, _) ->
      let c = cmp x v in
      if st c then (l, v, r)
      else if c < 0 then
        let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
      else
        let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
  in loop x tree

(* sprawdza, czy c należy do przedziału [x,y] *)
let w_przedziale x y c = c >= x && c <= y

(* funkcja wytnij zwraca dwa drzewa. Jedno z elementami mniejszymi od [a,b] i
  drugie z większymi. e1 i e2 to elementy z brzegów przedziału [a,b]. 
  np. w drzewie są elementy [1,2]; [5,9]; [11,12]; [15,17] 
  to funkcja wytnij dla przedziału [3,11] 
  zwróci (Empty, [1,2], [11,12], Drzewo([15,17]))
  Chcemy, żeby pierwszy split uwzględnił tylko przedziały styczne z lewej, 
  a drugi tylko styczne z prawej, dlatego st w pierwszym splt to 
  w_przedziale (-1) 0, a w drugim w_przedziale 0 1 *)
let wytnij x tree =
  match x with
  | Some(a, b) -> 
    let lr, e1, r = splt (Some(b, b)) tree (w_przedziale (-1) 0) in
    let l, e2, rl = splt (Some(a, a)) tree (w_przedziale 0 1) in
    (l, e2, e1, r)
  | _ -> invalid_arg "wytnij"

(* suma przedziałów *)
let rec suma x y =
  match x, y with
  | Some(a, b), Some(c, d) ->
    if a > c then suma (Some(c,d)) (Some(a,b))
    else Some(a,max b d) (* b >= c+1 *)
  | a, None | None, a -> a
    
(* zwraca drzewo tree wraz z przedziałem [a,b] *)
let rec add (a,b) tree =
  match tree with
  | Empty -> make Empty (Some(a,b)) Empty
  | Node(l, k, r, _, _) -> let c = cmp (Some(a,b)) k in
    if c < -1 then bal (add (a,b) l) k r
    else if c > 1 then bal l k (add (a,b) r)
    else let x = Some(a,b) in
      let l, e2, e1, r = wytnij x tree in
      let new_x = suma e2 (suma x e1) in
      join l new_x r

(* zwraca najmniejszy element w drzewie *)
let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(* zwraca drzewo bez najmniejszego elementu *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "remove_min_elt"

(* łączy dwa drzewa *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* różnica przedziłów
  jeśli różnica to więcej niż 1 przedział to dla s=-1 zwracamy mniejszy
  a dla s = 1 większy *)
let roznica x y s =
  match x, y with
  | Some(a, b), Some(c, d) ->
    if s = -1 then (if a = c then None else Some(a,c-1))
    else if b = d then None else Some(d+1,b)
  | a, _ -> a
  
(* zwraca drzewo tree z tymi samymi elementami poza elementami z przedziału [a,b] *)
let rec remove (a,b) tree =
  match tree with
  | Empty -> Empty
  | Node(l, k, r, _, _) ->
    let c = cmp (Some(a,b)) k in
    if c < 0 then bal (remove (a,b) l) k r
    else if c > 0 then bal l k (remove (a,b) r)
    else let x = Some(a,b) in
      let l, e2, e1, r = wytnij x tree in
      let e2 = roznica e2 x (-1) in
      let e1 = roznica e1 x 1 in
      add_one e2 (add_one e1 (merge l r))

(* sprawdza, czy x jest w tree *)
let mem x tree =
  let x = Some(x,x) in
  let rec loop = function
    | Node (l, k, r, _, _) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop tree

let iter f tree =
  let rec loop = function
    | Empty -> ()
    | Node (l, Some(a, b), r, _, _) -> loop l; f (a,b); loop r
    | _ -> invalid_arg "iter" in
  loop tree

let fold f tree acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, Some(a,b), r, _, _) ->
      loop (f (a,b) (loop acc l)) r
    | _ -> invalid_arg "fold" in
  loop acc tree

let elements tree = 
  let rec loop acc = function
    | Empty -> acc
    | Node(l, Some(a,b), r, _, _) -> loop ((a,b) :: loop acc r) l
    | _ -> invalid_arg "elements" in
  loop [] tree

let split a tree =
  let (l,p,r) = splt (Some(a,a)) tree (fun c -> c = 0) in
  let lp = roznica p (Some(a,a)) (-1) in
  let rp = roznica p (Some(a,a)) 1 in
  (add_one lp l, p <> None, add_one rp r)

let below n s =
  let rec counter s acc =
    match s with
    | Empty -> acc
    | Node(l, Some(a,b), r, _, s) ->
      let c = cmp (Some(n,n)) (Some(a,b)) in 
      if c = 0 then dodaj acc (dodaj (int_size a n) (size l))
      else if c < 0 then counter l acc
      else counter r (dodaj acc (dodaj (size l) (int_size a b)))
    | _ -> invalid_arg "below"
  in
  let ans = counter s max_int in
  max_int - ans

