
type k = None | Some of int * int 

type t =
  | Empty
  | Node of  t * k * t * int * int

let empty = Empty

let is_empty t = t = Empty

let rec cmp x y =
  match x, y with
  | Some(a,b), Some(c,d) -> 
    if a > c then -cmp (Some(c, d))  (Some(a,b))
    else if b >= c then 0
    else if b = c-1 then -1
    else -2
  | _ -> invalid_arg "cmp"

let height t =
  match t with
  | Node(_,_,_,h,_) -> h
  | Empty -> 0

let size t =
  match t with
  | Node(_,_,_,_,s) -> s
  | Empty -> max_int 

let int_size a b =
  let l = max 0 (max_int - b + a) - 1 in
  max l 0

let dodaj a b =
  let l = a - (max_int - b) in
  max l 0 

let make l k r =
  match k with
  | Some(a, b) ->
    let s = dodaj (size l) (dodaj (size r) (int_size a b) ) in
    Node (l, k, r, max (height l) (height r) + 1, s)
  | None -> invalid_arg "make"

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
  else make l k r (*Node (l, k, r, max hl hr + 1)*)

let rec add_one x tree =
  if x <> None then 
  match tree with
  | Node (l, k, r, h, s) ->
      let c = cmp x k in
      if c = 0 then Node (l, x, r, h, s)(* raczej nie powinno wystąpić *)
      else if c < 0 then
        let nl = add_one x l in
        bal nl k r
      else
        let nr = add_one x r in
        bal l k nr
  | Empty -> make Empty x Empty (*Node (Empty, x, Empty, 1)*)
  else tree

let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_one v r
  | (_, Empty) -> add_one v l
  | (Node(ll, lv, lr, lh, ls), Node(rl, rv, rr, rh, rs)) ->
    if lh > rh + 2 then bal ll lv (join lr v r) else
    if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

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

let w_przedziale x y c = c >= x && c <= y

let wytnij x tree =
  match x with
  | Some(a,b) -> 
    let lr, e1, r = splt (Some(b,b)) tree (w_przedziale (-1) 0) in
    let l, e2, rl = splt (Some(a,a)) tree (w_przedziale 0 1) in
    (l, e2, e1, r)
  | _ -> invalid_arg "wytnij"
  
let rec suma x y =
  match x, y with
  | Some(a, b), Some(c, d) ->
    if a > c then suma (Some(c,d)) (Some(a,b))
    else Some(a,d) (* b >= c+1 *)
  | a, None | None, a -> a

let add (a,b) tree =
  let x = Some(a,b) in
  let l, e2, e1, r = wytnij x tree in
  let new_x = suma e2 (suma x e1) in
  join l new_x r

let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "remove_min_elt"

let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* x i y to nie None oraz mają część wspólną *)
let roznica x y s =
  match x, y with
  | Some(a, b), Some(c, d) ->
    if s = -1 then (if a = c then None else Some(a,c-1))
    else if b = d then None else Some(d+1,b)
  | a, _ -> a
  
let remove (a,b) tree =
  let x = Some(a,b) in
  let l, e2, e1, r = wytnij x tree in
  let e2 = roznica e2 x (-1) in
  let e1 = roznica e1 x 1 in
  add_one e2 (add_one e1 (merge l r))

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

let split (a,b) tree =
  let (l,p,r) = splt (Some(a,b)) tree (fun c -> c = 0) in
  (l, p <> None, r)

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
