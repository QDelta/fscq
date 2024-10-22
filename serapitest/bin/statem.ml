module type ST = sig
  type st
end

module Make (T : ST) = struct
  type 'a t = T.st -> 'a * T.st

  let run (r : 'a t) (init : T.st) : 'a = fst (r init)
  let exec (r : 'a t) (init : T.st) : T.st = snd (r init)
  let update (f : T.st -> T.st) : unit t = fun s -> ((), f s)
  let get : T.st t = fun s -> (s, s)

  let ( let* ) (r1 : 'a t) (f : 'a -> 'b t) : 'b t =
   fun s1 ->
    let x, s2 = r1 s1 in
    let r2 = f x in
    r2 s2

  let return (x : 'a) : 'a t = fun s -> (x, s)

  let ( $ ) f r =
    let* x = r in
    return (f x)

  let ( >> ) (r1 : 'a t) (f : 'b t) : 'b t =
    let* _ = r1 in
    f

  let rec mapM (f : 'a -> 'b t) (l : 'a list) : 'b list t =
    match l with
    | [] -> return []
    | x :: xs ->
        let* y = f x in
        let* ys = mapM f xs in
        return (y :: ys)
end
