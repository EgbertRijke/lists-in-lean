/- This is a short tutorial on lean for the Logic in Computer Science course at the university
of Ljubljana. -/

namespace logika_v_racunalnistvu 

/- We typically want to be universe polymorphic in lean, so we introduce a universe variable u. -/

universes u v w 

/- Definitions of inductive types are made using the inductive keyword. Different constructors
   are separated by |. -/

inductive list (A : Type u) : Type u
| nil : list
| cons : A → list → list

/- We open the namespace list, so that we can use nil and cons directly. -/

namespace list

/- We will now define some basic operations on lists. -/

/- Direct definitions are made using the definition keyword, followed by := -/

definition unit {A : Type u} (a : A) : list A :=
cons a nil

/- A shorthand for definition is def, which may also be used. -/

/- Since the type of lists is an inductive type, we can make inductive definitions on list
using pattern matching. The syntax is analogous to the syntax of the inductive type itself. 
Note that in pattern matching definitions, we don't use := at the end of the specification. -/

def fold {A : Type u} {B : Type v} (b : B) (μ : A → B → B) : list A → B
| nil := b
| (cons a l) := μ a (fold l)

def functor_list {A : Type u} {B : Type v} (f : A → B) : list A → list B 
| nil := nil
| (cons a x) := cons (f a) (functor_list x)

def length {A : Type u} : list A → ℕ :=
fold 0 (λ _ n, n + 1)

def sum_list_ℕ : list ℕ → ℕ :=
fold 0 (λ m n, m + n)

def concat {A : Type u} : list A → list A → list A :=
fold id (λ a f l, cons a (f l))

def flatten {A : Type u} : list (list A) → list A :=
fold nil concat 

def reverse {A : Type u} : list A → list A
| nil := nil
| (cons a l) := concat (reverse l) (unit a)

/- We have now finished defining our basic operations on lists. Let us check by some examples 
   that the operations indeed do what they are supposed to do. With your mouse, hover over the
   #reduce keyword to see what each term reduces to. -/

#reduce concat (cons 1 (cons 2 (cons 3 nil))) (cons 4 (cons 5 nil))

#reduce sum_list_ℕ (concat (cons 1 (cons 2 (cons 3 nil))) (cons 4 (cons 5 nil)))

#reduce reverse (concat (cons 1 (cons 2 (cons 3 nil))) (cons 4 (cons 5 nil)))

/- Of course, if you really want to know that your operations behave as expected, you should 
   prove the relevant properties about them. This is what we will do next. -/

/- When proving theorems, we can also proceed by pattern matching. In a pattern matching argument
   we can recursively call the object we are defining on earlier instances.
   
   The arguments that we want to pattern-match on, must appear after the colon (:) in the 
   specification of the theorem. -/

theorem identity_law_functor_list {A : Type u} :
    ∀ (x : list A), functor_list id x = x 
| nil := rfl
| (cons a x) := 
    calc
    functor_list id (cons a x) 
        = cons a (functor_list id x) : rfl
    ... = cons a x : by rw identity_law_functor_list

theorem composition_law_functor_list {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C) :
    ∀ (x : list A), functor_list (g ∘ f) x = functor_list g (functor_list f x)
| nil := rfl
| (cons a x) := 
    calc
    functor_list (g ∘ f) (cons a x)
        = cons (g (f a)) (functor_list (g ∘ f) x) : rfl 
    ... = cons (g (f a)) (functor_list g (functor_list f x)) : by rw composition_law_functor_list
    ... = functor_list g (functor_list f (cons a x)) : rfl   

/- Next, we prove some properties concatenation. Concatenation of lists is an associative
   operation, and it satisfies the left and right unit laws.universe
   
   In order to prove associativity, we note that since concatenation is defined by induction
   on the left argument, we will again use induction on the left argument to prove this 
   propoerty. The proof is presented by pattern matching.
   
   In the proof we will use the built-in equation compiler. We just calculate as if we were
   working on a sheet of paper, and each time we mention the reason why the equality holds. -/

theorem assoc_concat {A : Type u} : 
    ∀ (x y z : list A), concat (concat x y) z = concat x (concat y z)
| nil _ _ := rfl
| (cons a l) y z :=
    calc
    concat (concat (cons a l) y) z 
        = cons a (concat (concat l y) z) : by reflexivity
    ... = cons a (concat l (concat y z)) : by rw assoc_concat
    ... = concat (cons a l) (concat y z) : by reflexivity

theorem left_unit_law_concat {A : Type u} : 
    ∀ (x : list A), concat nil x = x := 
    eq.refl 

theorem right_unit_law_concat {A : Type u} : 
    ∀ (x : list A), concat x nil = x 
| nil := rfl
| (cons a x) := 
    show cons a (concat x nil) = cons a x, 
    by rw right_unit_law_concat 

/- Next, we prove the elementary properties of the length function. -/

theorem length_nil {A : Type u} :
    length (@nil A) = 0 := rfl

theorem length_unit {A : Type u} (a : A) :
    length (unit a) = 1 :=
    rfl

theorem length_concat {A : Type u} :
    ∀ (x y : list A), length (concat x y) = length x + length y
| nil y := 
    calc
    length (concat nil y) 
        = length y : rfl
    ... = 0 + length y : by rw zero_add
    ... = length nil + length y : by rw length_nil
| (cons a x) y :=
    calc
    length (concat (cons a x) y)
        = length (concat x y) + 1 : rfl
    ... = (length x + length y) + 1 : by rw length_concat
    ... = (length x + 1) + length y : by rw nat.succ_add
    ... = (length (cons a x)) + length y : rfl

/- Next, we prove the elemenatary properties of the flatten function. -/

theorem flatten_unit {A : Type u} :
    ∀ (x : list A), flatten (unit x) = x := 
    right_unit_law_concat

theorem length_flatten {A : Type u} :
    ∀ (x : list (list A)), length (flatten x) = sum_list_ℕ (functor_list length x)
| nil := rfl
| (cons a x) := 
    calc
    length (flatten (cons a x)) 
        = length (concat a (flatten x)) : rfl
    ... = length a + length (flatten x) : by rw length_concat 
    ... = length a + sum_list_ℕ (functor_list length x) : by rw length_flatten 
    ... = sum_list_ℕ (functor_list length (cons a x)) : rfl 

theorem flatten_concat {A : Type u} :
    ∀ (x y : list (list A)), flatten (concat x y) = concat (flatten x) (flatten y)
| nil y := rfl
| (cons a x) y := 
    calc
    flatten (concat (cons a x) y) 
        = concat a (flatten (concat x y)) : rfl
    ... = concat a (concat (flatten x) (flatten y)) : by rw flatten_concat
    ... = concat (concat a (flatten x)) (flatten y) : by rw assoc_concat
    ... = concat (flatten (cons a x)) (flatten y) : rfl 

theorem flatten_flatten {A : Type u} :
    ∀ (x : list (list (list A))), flatten (flatten x) = flatten (functor_list flatten x)
| nil := rfl
| (cons a x) := 
    calc
    flatten (flatten (cons a x))
        = flatten (concat a (flatten x)) : rfl
    ... = concat (flatten a) (flatten (flatten x)) : by rw flatten_concat
    ... = concat (flatten a) (flatten (functor_list flatten x)) : by rw flatten_flatten 
    ... = flatten (functor_list flatten (cons a x)) : rfl 

/- Next, we prove the elementary properties of list reversal. -/

theorem unit_reverse {A : Type u} (a : A) :
    reverse (unit a) = unit a := rfl 

theorem length_reverse {A : Type u} : 
    ∀ (x : list A), length (reverse x) = length x
| nil := rfl
| (cons a x) := 
    calc
    length (reverse (cons a x)) 
        = length (concat (reverse x) (unit a)) : rfl
    ... = length (reverse x) + length (unit a) : by rw length_concat
    ... = length (reverse x) + 1 : by rw length_unit
    ... = length x + 1 : by rw length_reverse
    ... = length (cons a x) : rfl 

theorem reverse_concat {A : Type u} : 
    ∀ (x y : list A), reverse (concat x y) = concat (reverse y) (reverse x)
| nil y := 
    calc 
    reverse (concat nil y) = reverse y : by reflexivity
    ... = concat (reverse y) nil : by rw right_unit_law_concat
| (cons a x) y :=
    calc 
    reverse (concat (cons a x) y)
        = concat (reverse (concat x y)) (unit a) : rfl
    ... = concat (concat (reverse y) (reverse x)) (unit a) : by rw reverse_concat
    ... = concat (reverse y) (concat (reverse x) (unit a)) : by rw assoc_concat
    ... = concat (reverse y) (reverse (cons a x)) : rfl

theorem reverse_flatten {A : Type u} :
    ∀ (x : list (list A)), reverse (flatten x) = flatten (reverse (functor_list reverse x))
| nil := rfl
| (cons a x) := 
    calc
    reverse (flatten (cons a x))
        = reverse (concat a (flatten x)) : rfl
    ... = concat (reverse (flatten x)) (reverse a) : by rw reverse_concat
    ... = concat (flatten (reverse (functor_list reverse x))) (reverse a) : by rw reverse_flatten
    ... = concat (flatten (reverse (functor_list reverse x))) (flatten (unit (reverse a))) : by rw flatten_unit 
    ... = flatten (concat (reverse (functor_list reverse x)) (unit (reverse a))) : by rw flatten_concat
    ... = flatten (reverse (cons (reverse a) (functor_list reverse x))) : rfl 
    ... = flatten (reverse (functor_list reverse (cons a x))) : rfl

theorem reverse_reverse {A : Type u} : 
    ∀ (x : list A), reverse (reverse x) = x 
| nil := rfl
| (cons a x) := 
    calc
    reverse (reverse (cons a x)) 
        = reverse (concat (reverse x) (unit a)) : rfl
    ... = concat (reverse (unit a)) (reverse (reverse x)) : by rw reverse_concat 
    ... = concat (unit a) (reverse (reverse x)) : by rw unit_reverse
    ... = concat (unit a) x : by rw reverse_reverse
    ... = cons a x : rfl 

/- The next topic of our study of lists is Heads and Tails -/

def head {A : Type u} : list A → list A
| nil := nil  
| (cons a x) := unit a

/- Note that the type of head can't be list A → A, because we might apply head to the empty list
   In that case, we should allow for an exception. Instead of mapping to the coproduct A + 1, we 
   make give head the type list A → list A. -/

def tail {A : Type u} : list A → list A 
| nil := nil 
| (cons a x) := x 

/- If we concatenate the head with the tail, we get the original list back -/

def concat_head_tail {A : Type u} : 
    ∀ (x : list A), concat (head x) (tail x) = x 
| nil := rfl 
| (cons a x) := rfl 

theorem head_head {A : Type u} : 
    ∀ (x : list A), head (head x) = head x
| nil := rfl 
| (cons a x) := rfl 

theorem head_concat {A : Type u} : 
    ∀ (x y : list A), head (concat x y) = head (concat (head x) (head y)) 
| nil y := 
    calc 
    head (concat nil y) 
        = head y : rfl 
    ... = head (head y) : by rw head_head  
    ... = head (concat (head nil) (head y)) : rfl 
| (cons a x) y := rfl 

theorem tail_concat {A : Type u} :
    ∀ (x y : list A), tail (concat x y) = concat (tail x) (tail (concat (head x) y))
| nil y := rfl 
| (cons a x) y := 
    calc 
    tail (concat (cons a x) y)
        = tail (cons a (concat x y)) : rfl
    ... = tail (cons a (concat (tail (cons a x)) y)) : rfl 
    ... = concat (tail (cons a x)) y : rfl 
    ... = concat (tail (cons a x)) (tail (concat (head (cons a x)) y)) : rfl 

/- Dual to taking the head of a list, we may take the last element of a list. -/

def last {A : Type u} : list A → list A
| nil := nil  
| (cons a nil) := unit a 
| (cons a (cons a' x')) := last (cons a' x')

/- The last element is of course the head of the reversed list. -/

theorem head_reverse {A : Type u} : 
    ∀ (x : list A), head (reverse x) = last x 
| nil := rfl 
| (cons a nil) := rfl
| (cons a (cons a' x')) := 
    calc
    head (reverse (cons a (cons a' x'))) 
        = head (concat (reverse (cons a' x')) (unit a)) : rfl
    ... = head (concat (concat (reverse x') (unit a')) (unit a)) : rfl
    ... = head (concat (reverse x') (concat (unit a') (unit a))) : by rw assoc_concat 
    ... = head (concat (head (reverse x')) (head (concat (unit a') (unit a)))) : by rw head_concat
    ... = head (concat (head (reverse x')) (head (unit a'))) : rfl 
    ... = head (concat (reverse x') (unit a')) : by {symmetry, rw head_concat}
    ... = head (reverse (cons a' x')) : rfl
    ... = last (cons a' x') : by rw head_reverse
    ... = last (cons a (cons a' x')) : rfl

/- Dual to taking the tail of a list, we may remove the last element of the list. -/

def remove_last {A : Type u} : list A → list A
| nil := nil
| (cons a nil) := nil 
| (cons a (cons a' x')) := cons a (remove_last (cons a' x')) 

/- Removing the last element of the list is of course taking the reverse of the tail of the 
   reverse. -/

theorem tail_concat' {A : Type u} :
    ∀ (x  y : list A), 
    tail (concat x y) = concat (tail x) (tail (concat (last x) y))
| nil y := rfl
| (cons a nil) y := rfl 
| (cons a (cons a' x')) y :=
    calc
    tail (concat (cons a (cons a' x')) y) 
        = concat (cons a' x') y : rfl
    ... = cons a' (tail (concat (cons a' x') y)) : rfl
    ... = cons a' (concat (tail (cons a' x')) (tail (concat (last (cons a' x')) y))) : by rw tail_concat' 
    ... = concat (cons a' x') (tail (concat (last (cons a' x')) y)) : rfl 
    ... = concat (tail (cons a (cons a' x'))) (tail (concat (last (cons a (cons a' x'))) y)) : rfl

def cons' {A : Type u} (x : list A) (a : A) : list A :=
concat x (unit a)

theorem last_cons' {A : Type u} : 
    ∀ (x : list A) (a : A), last (cons' x a) = unit a
| nil a := rfl
| (cons a' nil) a := rfl
| (cons a' (cons a'' x'')) a :=
    calc
    last (cons' (cons a' (cons a'' x'')) a) 
        = last (cons a' (cons a'' (concat x'' (unit a)))) : rfl
    ... = last (cons a'' (concat x'' (unit a))) : rfl 
    ... = last (cons' (cons a'' x'') a) : rfl 
    ... = unit a : by rw last_cons'  

theorem tail_reverse {A : Type u} : 
    ∀ (x : list A), tail (reverse x) = reverse (remove_last x)
| nil := rfl
| (cons a nil) := rfl 
| (cons a (cons a' x')) :=
    calc
    tail (reverse (cons a (cons a' x')))
        = tail (concat (reverse (cons a' x')) (unit a)) : rfl 
    ... = concat 
            ( tail (reverse (cons a' x'))) 
            ( tail (concat (last (reverse (cons a' x'))) (unit a))) : by rw tail_concat' 
    ... = concat 
            ( tail (reverse (cons a' x')))
            ( tail (concat (last (concat (reverse x') (unit a'))) (unit a))) : rfl
    ... = concat 
            ( tail (reverse (cons a' x')))
            ( tail (concat (last (cons' (reverse x') a')) (unit a))) : rfl
    ... = concat
            ( tail (reverse (cons a' x')))
            ( tail (concat (unit a') (unit a))) : by rw last_cons' 
    ... = concat (tail (reverse (cons a' x'))) (unit a) : rfl
    ... = concat (reverse (remove_last (cons a' x'))) (unit a) : by rw tail_reverse
    ... = reverse (cons a (remove_last (cons a' x'))) : rfl
    ... = reverse (remove_last (cons a (cons a' x'))) : rfl

theorem remove_last_reverse {A : Type u} (x : list A):
    remove_last (reverse x) = reverse (tail x) := 
calc
remove_last (reverse x)
    = reverse (reverse (remove_last (reverse x))) : by rw reverse_reverse
... = reverse (tail (reverse (reverse x))) : by rw tail_reverse
... = reverse (tail x) : by {symmetry, rw reverse_reverse}

end list 

/- Next, we study lists of a fixed length. -/

inductive list_of_length (A : Type u) : ℕ → Type u 
| nil : list_of_length 0
| cons : ∀ (n : ℕ), A → list_of_length n → list_of_length (n+1)

namespace list_of_length

theorem eq_nil {A : Type u} : ∀ (x : list_of_length A 0), x = nil 
| nil := rfl 

def functor {A : Type u} {B : Type v} (f : A → B) :
    ∀ (n : ℕ), list_of_length A n → list_of_length B n 
| 0 nil := nil
| (n+1) (cons n' a x) := cons n' (f a) (functor n' x)

def head {A : Type u} :
    ∀ (n : ℕ), list_of_length A (n+1) → A 
| n (cons n' a x) := a 

def tail {A : Type u} : 
    ∀ (n : ℕ), list_of_length A (n+1) → list_of_length A n 
| n (cons n' a x) := x 

/- Using lists of fixed length, we can define matrices. The type
   Matrix m n A is the type of matrices with m rows and n columns
   and with coefficients in A. -/

def Matrix (m n : ℕ) (A : Type u) : Type u :=
list_of_length (list_of_length A n) m

def top_row {A : Type u} {m n : ℕ} : 
    Matrix (m+1) n A → list_of_length A n := 
head m 

def tail_vertical {A : Type u} {m n : ℕ} : 
    Matrix (m+1) n A → Matrix m n A :=
tail m 

def left_column {A : Type u} {m n : ℕ} :
    Matrix m (n+1) A → list_of_length A m := 
functor (head n) m

def tail_horizontal {A : Type u} {m n : ℕ} : 
    Matrix m (n+1) A → Matrix m n A :=
functor (tail n) m

/- Since matrices are rectangular, we have a horizontal as well as vertical empty matrices. -/

def nil_vertical {A : Type u} {n : ℕ} : Matrix 0 n A := nil

theorem eq_nil_vertical {A : Type u} : 
    ∀ {n : ℕ} (x : Matrix 0 n A), x = nil_vertical
| 0 nil := rfl 
| (n+1) nil := rfl  

def nil_horizontal {A : Type u} : ∀ {m : ℕ}, Matrix m 0 A 
| 0 := nil 
| (m+1) := cons m nil nil_horizontal

theorem eq_nil_horizontal {A : Type u} : 
    ∀ {m : ℕ} (x : Matrix m 0 A), x = nil_horizontal
| 0 nil := rfl 
| (m+1) (cons m' nil M) := 
    calc
    cons m nil M 
        = cons m nil nil_horizontal : by rw eq_nil_horizontal M  
    ... = nil_horizontal : rfl

/- Similarly, there is a horizontal cons and a vertical cons. -/

/- cons_vertical adds a new row from the top. -/

def cons_vertical {A : Type u} {m n : ℕ} :
    list_of_length A n → Matrix m n A → Matrix (m+1) n A :=
    cons m

theorem top_row_cons_vertical 
    {A : Type u} {m n : ℕ} (x : list_of_length A n) (M : Matrix m n A) :
    top_row (cons_vertical x M) = x := 
rfl 

theorem left_colum_cons_vertical {A : Type u} :
    ∀ {m n : ℕ} (x : list_of_length A (n+1)) (M : Matrix m (n+1) A),
    left_column (cons_vertical x M) = cons m (head n x) (left_column M)
| m n (cons n' a x) M := rfl 

theorem eta_vertical {A : Type u} :
    ∀ {m n : ℕ} (M : Matrix (m+1) n A), 
    cons_vertical (top_row M) (tail_vertical M) = M
| m n (cons _ x M) := rfl 

/- cons_horizontal adds a new column from the left. -/

def cons_horizontal {A : Type u} :
    ∀ {m n : ℕ}, list_of_length A m → Matrix m n A → Matrix m (n+1) A 
| 0 n nil M := nil
| (m+1) n (cons m' a x) M := 
    cons m (cons n a (top_row M)) (cons_horizontal x (tail_vertical M))

theorem left_column_cons_horizontal {A : Type u} :
    ∀ {m n : ℕ} (x : list_of_length A m) (M : Matrix m n A),
    left_column (cons_horizontal x M) = x 
| 0 n nil M := rfl 
| (m+1) n (cons m' a x) M := 
    calc
    left_column (cons_horizontal (cons m' a x) M)
        = cons m a (left_column (cons_horizontal x (tail_vertical M))) : rfl  
    ... = cons m a x : by rw left_column_cons_horizontal 

theorem top_row_cons_horizontal {A : Type u} :
    ∀ {m n : ℕ} (x : list_of_length A (m+1)) (M : Matrix (m+1) n A),
    top_row (cons_horizontal x M) = cons n (head m x) (top_row M)
| m n (cons m' a x) (cons m'' y M) := rfl 

theorem tail_vertical_cons_horizontal {A : Type} :
    ∀ {m n : ℕ} (x : list_of_length A (m+1)) (M : Matrix (m+1) n A),
    tail_vertical (cons_horizontal x M) = cons_horizontal (tail m x) (tail_vertical M)
| m n (cons m' a x) (cons m'' y M) := rfl 

theorem eta_horizontal {A : Type u} :
    ∀ {m n : ℕ} (M : Matrix m (n+1) A),
    cons_horizontal (left_column M) (tail_horizontal M) = M 
| 0 n nil := rfl
| (m+1) n (cons m' (cons n' a x) M) :=
    calc
    cons_horizontal (left_column (cons m (cons n a x) M)) (tail_horizontal (cons m (cons n a x) M))
        = cons m (cons n a x) (cons_horizontal (left_column M) (tail_horizontal M)) : rfl
    ... = cons m (cons n a x) M : by rw eta_horizontal M

/- Next we show that if we add a row from the top as well as a column from the left, then it 
   doesn't matter in which order we do that. -/

theorem cons_horizontal_cons_vertical {A : Type u} :
    ∀ {m n : ℕ} (a : A) (x : list_of_length A n) (y : list_of_length A m) (M : Matrix m n A),
    cons_horizontal (cons m a y) (cons_vertical x M) 
        = cons_vertical (cons n a x) (cons_horizontal y M) 
| m n a x y M := rfl 

/- We define the transposition of a matrix. -/

def transpose {A : Type u} : 
    ∀ {m n : ℕ}, Matrix m n A → Matrix n m A
| 0 n M := nil_horizontal
| (m+1) n (cons m' x M) := cons_horizontal x (transpose M)

/- The following three theorems show how transpose interacts with the basic operations on
   matrices. These will help to show that transposition is an involution. -/

theorem transpose_nil {A : Type u} :
    ∀ {n : ℕ}, @transpose A 0 n nil = nil_horizontal 
| 0 := rfl 
| (n+1) := rfl 

theorem transpose_cons_horizontal {A : Type u} :
    ∀ {m n : ℕ} (x : list_of_length A m) (M : Matrix m n A),
    transpose (cons_horizontal x M) = cons_vertical x (transpose M)
| 0 n nil M := rfl 
| (m+1) n (cons m' a x) (cons m'' y M) := 
    calc
    transpose (cons_horizontal (cons m' a x) (cons m'' y M))
        = transpose (cons m (cons n a y) (cons_horizontal x M)) : rfl 
    ... = cons_horizontal (cons n a y) (transpose (cons_horizontal x M)) : rfl 
    ... = cons_horizontal (cons n a y) (cons_vertical x (transpose M)) : by rw transpose_cons_horizontal
    ... = cons_vertical (cons m a x) (transpose (cons m y M)) : by reflexivity

theorem transpose_cons_vertical {A : Type u} :
    ∀ {m n : ℕ} (x : list_of_length A n) (M : Matrix m n A),
    transpose (cons_vertical x M) = cons_horizontal x (transpose M)
| m n x M := rfl 

/- We finally show that transposition is an involution. -/

theorem transpose_transpose {A : Type u} :
    ∀ (m n : ℕ) (M : Matrix m n A), transpose (transpose M) = M
| 0 0 nil := rfl
| 0 (n+1) nil := rfl 
| (m+1) 0 M := 
    calc
    transpose (transpose M) 
        = transpose nil : rfl 
    ... = nil_horizontal : by rw transpose_nil
    ... = M : by rw eq_nil_horizontal M
| (m+1) (n+1) (cons _ x M) := 
    calc
    transpose (transpose (cons _ x M))
        = transpose (transpose (cons_vertical x M)) : rfl 
    ... = transpose (cons_horizontal x (transpose M)) : by rw transpose_cons_vertical
    ... = cons_vertical x (transpose (transpose M)) : by rw transpose_cons_horizontal
    ... = cons_vertical x M : by rw transpose_transpose
    ... = cons _ x M : rfl

end list_of_length

end logika_v_racunalnistvu