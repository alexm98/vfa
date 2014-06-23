type nat =
| O
| S of nat

type key = int

module type SET_OF_ORDERED = 
 sig 
  type set 
  
  val empty : set
  
  val member : key -> set -> bool
  
  val insert : key -> set -> set
 end

module RedBlackTree = 
 struct 
  type color =
  | Red
  | Black
  
  (** val color_rect : 'a1 -> 'a1 -> color -> 'a1 **)
  
  let color_rect f f0 = function
  | Red -> f
  | Black -> f0
  
  (** val color_rec : 'a1 -> 'a1 -> color -> 'a1 **)
  
  let color_rec f f0 = function
  | Red -> f
  | Black -> f0
  
  type tree =
  | E
  | T of color * tree * key * tree
  
  (** val tree_rect :
      'a1 -> (color -> tree -> 'a1 -> key -> tree -> 'a1 -> 'a1) -> tree ->
      'a1 **)
  
  let rec tree_rect f f0 = function
  | E -> f
  | T (c, t0, k, t1) -> f0 c t0 (tree_rect f f0 t0) k t1 (tree_rect f f0 t1)
  
  (** val tree_rec :
      'a1 -> (color -> tree -> 'a1 -> key -> tree -> 'a1 -> 'a1) -> tree ->
      'a1 **)
  
  let rec tree_rec f f0 = function
  | E -> f
  | T (c, t0, k, t1) -> f0 c t0 (tree_rec f f0 t0) k t1 (tree_rec f f0 t1)
  
  (** val member : key -> tree -> bool **)
  
  let rec member x = function
  | E -> false
  | T (c, tl, k, tr) ->
    if (<) x k then member x tl else if (<) k x then member x tr else true
  
  (** val balance : color -> tree -> key -> tree -> tree **)
  
  let balance rb t1 k t2 =
    match rb with
    | Red -> T (Red, t1, k, t2)
    | Black ->
      (match t1 with
       | E ->
         (match t2 with
          | E -> T (Black, t1, k, t2)
          | T (c0, b, y, d) ->
            (match c0 with
             | Red ->
               (match b with
                | E ->
                  (match d with
                   | E -> T (Black, t1, k, t2)
                   | T (c1, c, z, d0) ->
                     (match c1 with
                      | Red ->
                        T (Red, (T (Black, t1, k, b)), y, (T (Black, c, z,
                          d0)))
                      | Black -> T (Black, t1, k, t2)))
                | T (c1, b0, y0, c) ->
                  (match c1 with
                   | Red ->
                     T (Red, (T (Black, t1, k, b0)), y0, (T (Black, c, y,
                       d)))
                   | Black ->
                     (match d with
                      | E -> T (Black, t1, k, t2)
                      | T (c2, c3, z, d0) ->
                        (match c2 with
                         | Red ->
                           T (Red, (T (Black, t1, k, b)), y, (T (Black, c3,
                             z, d0)))
                         | Black -> T (Black, t1, k, t2)))))
             | Black -> T (Black, t1, k, t2)))
       | T (c0, a, x, c) ->
         (match c0 with
          | Red ->
            (match a with
             | E ->
               (match c with
                | E ->
                  (match t2 with
                   | E -> T (Black, t1, k, t2)
                   | T (c1, b, y, d) ->
                     (match c1 with
                      | Red ->
                        (match b with
                         | E ->
                           (match d with
                            | E -> T (Black, t1, k, t2)
                            | T (c2, c3, z, d0) ->
                              (match c2 with
                               | Red ->
                                 T (Red, (T (Black, t1, k, b)), y, (T (Black,
                                   c3, z, d0)))
                               | Black -> T (Black, t1, k, t2)))
                         | T (c2, b0, y0, c3) ->
                           (match c2 with
                            | Red ->
                              T (Red, (T (Black, t1, k, b0)), y0, (T (Black,
                                c3, y, d)))
                            | Black ->
                              (match d with
                               | E -> T (Black, t1, k, t2)
                               | T (c4, c5, z, d0) ->
                                 (match c4 with
                                  | Red ->
                                    T (Red, (T (Black, t1, k, b)), y, (T
                                      (Black, c5, z, d0)))
                                  | Black -> T (Black, t1, k, t2)))))
                      | Black -> T (Black, t1, k, t2)))
                | T (c1, b, y, c2) ->
                  (match c1 with
                   | Red ->
                     T (Red, (T (Black, a, x, b)), y, (T (Black, c2, k, t2)))
                   | Black ->
                     (match t2 with
                      | E -> T (Black, t1, k, t2)
                      | T (c3, b0, y0, d) ->
                        (match c3 with
                         | Red ->
                           (match b0 with
                            | E ->
                              (match d with
                               | E -> T (Black, t1, k, t2)
                               | T (c4, c5, z, d0) ->
                                 (match c4 with
                                  | Red ->
                                    T (Red, (T (Black, t1, k, b0)), y0, (T
                                      (Black, c5, z, d0)))
                                  | Black -> T (Black, t1, k, t2)))
                            | T (c4, b1, y1, c5) ->
                              (match c4 with
                               | Red ->
                                 T (Red, (T (Black, t1, k, b1)), y1, (T
                                   (Black, c5, y0, d)))
                               | Black ->
                                 (match d with
                                  | E -> T (Black, t1, k, t2)
                                  | T (c6, c7, z, d0) ->
                                    (match c6 with
                                     | Red ->
                                       T (Red, (T (Black, t1, k, b0)), y0, (T
                                         (Black, c7, z, d0)))
                                     | Black -> T (Black, t1, k, t2)))))
                         | Black -> T (Black, t1, k, t2)))))
             | T (c1, a0, x0, b) ->
               (match c1 with
                | Red ->
                  T (Red, (T (Black, a0, x0, b)), x, (T (Black, c, k, t2)))
                | Black ->
                  (match c with
                   | E ->
                     (match t2 with
                      | E -> T (Black, t1, k, t2)
                      | T (c2, b0, y, d) ->
                        (match c2 with
                         | Red ->
                           (match b0 with
                            | E ->
                              (match d with
                               | E -> T (Black, t1, k, t2)
                               | T (c3, c4, z, d0) ->
                                 (match c3 with
                                  | Red ->
                                    T (Red, (T (Black, t1, k, b0)), y, (T
                                      (Black, c4, z, d0)))
                                  | Black -> T (Black, t1, k, t2)))
                            | T (c3, b1, y0, c4) ->
                              (match c3 with
                               | Red ->
                                 T (Red, (T (Black, t1, k, b1)), y0, (T
                                   (Black, c4, y, d)))
                               | Black ->
                                 (match d with
                                  | E -> T (Black, t1, k, t2)
                                  | T (c5, c6, z, d0) ->
                                    (match c5 with
                                     | Red ->
                                       T (Red, (T (Black, t1, k, b0)), y, (T
                                         (Black, c6, z, d0)))
                                     | Black -> T (Black, t1, k, t2)))))
                         | Black -> T (Black, t1, k, t2)))
                   | T (c2, b0, y, c3) ->
                     (match c2 with
                      | Red ->
                        T (Red, (T (Black, a, x, b0)), y, (T (Black, c3, k,
                          t2)))
                      | Black ->
                        (match t2 with
                         | E -> T (Black, t1, k, t2)
                         | T (c4, b1, y0, d) ->
                           (match c4 with
                            | Red ->
                              (match b1 with
                               | E ->
                                 (match d with
                                  | E -> T (Black, t1, k, t2)
                                  | T (c5, c6, z, d0) ->
                                    (match c5 with
                                     | Red ->
                                       T (Red, (T (Black, t1, k, b1)), y0, (T
                                         (Black, c6, z, d0)))
                                     | Black -> T (Black, t1, k, t2)))
                               | T (c5, b2, y1, c6) ->
                                 (match c5 with
                                  | Red ->
                                    T (Red, (T (Black, t1, k, b2)), y1, (T
                                      (Black, c6, y0, d)))
                                  | Black ->
                                    (match d with
                                     | E -> T (Black, t1, k, t2)
                                     | T (c7, c8, z, d0) ->
                                       (match c7 with
                                        | Red ->
                                          T (Red, (T (Black, t1, k, b1)), y0,
                                            (T (Black, c8, z, d0)))
                                        | Black -> T (Black, t1, k, t2)))))
                            | Black -> T (Black, t1, k, t2)))))))
          | Black ->
            (match t2 with
             | E -> T (Black, t1, k, t2)
             | T (c1, b, y, d) ->
               (match c1 with
                | Red ->
                  (match b with
                   | E ->
                     (match d with
                      | E -> T (Black, t1, k, t2)
                      | T (c2, c3, z, d0) ->
                        (match c2 with
                         | Red ->
                           T (Red, (T (Black, t1, k, b)), y, (T (Black, c3,
                             z, d0)))
                         | Black -> T (Black, t1, k, t2)))
                   | T (c2, b0, y0, c3) ->
                     (match c2 with
                      | Red ->
                        T (Red, (T (Black, t1, k, b0)), y0, (T (Black, c3, y,
                          d)))
                      | Black ->
                        (match d with
                         | E -> T (Black, t1, k, t2)
                         | T (c4, c5, z, d0) ->
                           (match c4 with
                            | Red ->
                              T (Red, (T (Black, t1, k, b)), y, (T (Black,
                                c5, z, d0)))
                            | Black -> T (Black, t1, k, t2)))))
                | Black -> T (Black, t1, k, t2)))))
  
  (** val makeBlack : tree -> tree **)
  
  let makeBlack = function
  | E -> E
  | T (c, a, x, b) -> T (Black, a, x, b)
  
  (** val ins : key -> tree -> tree **)
  
  let rec ins x = function
  | E -> T (Red, E, x, E)
  | T (c, a, y, b) ->
    if (<) x y
    then balance c (ins x a) y b
    else if (<) y x then balance c a y (ins x b) else T (c, a, x, b)
  
  (** val insert : key -> tree -> tree **)
  
  let insert x s =
    makeBlack (ins x s)
  
  (** val interp'_rect : tree -> key -> 'a1 **)
  
  let interp'_rect t k =
    assert false (* absurd case *)
  
  (** val interp'_rec : tree -> key -> 'a1 **)
  
  let interp'_rec t k =
    assert false (* absurd case *)
  
  (** val nearly_redblack_rect : tree -> nat -> 'a1 **)
  
  let nearly_redblack_rect t n =
    assert false (* absurd case *)
  
  (** val nearly_redblack_rec : tree -> nat -> 'a1 **)
  
  let nearly_redblack_rec t n =
    assert false (* absurd case *)
  
  type set = tree
  
  (** val empty : tree **)
  
  let empty =
    E
 end

