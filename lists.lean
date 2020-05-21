/- This is a short tutorial on lean for the Logic in Computer Science course at the university
of Ljubljana. -/

namespace logika_v_racunalnistvu 

/- Definitions of inductive types are made using the inductive keyword. Different constructors
   are separated by |. -/

inductive list (A : Type) : Type
| nil : list
| cons : A → list → list

/- We open the namespace list, so that we can use nil and cons directly. -/

namespace list

/- We will now define some basic operations on lists. -/

/- Direct definitions are made using the definition keyword, followed by := -/

definition unit {A : Type} (a : A) : list A :=
cons a nil

/- A shorthand for definition is def, which may also be used. -/

/- Since the type of lists is an inductive type, we can make inductive definitions on list
using pattern matching. The syntax is analogous to the syntax of the inductive type itself. 
Note that in pattern matching definitions, we don't use := at the end of the specification. -/

def fold {A : Type} {B : Type} (b : B) (μ : A → B → B) : list A → B
| nil := b
| (cons a l) := μ a (fold l)

def map {A : Type} {B : Type} (f : A → B) : list A → list B :=
fold nil (cons ∘ f)

def length {A : Type} : list A → ℕ :=
fold 0 (λ _ n, n + 1)

def sum_list_ℕ : list ℕ → ℕ :=
fold 0 (λ m n, m + n)

def concat {A : Type} : list A → list A → list A :=
fold id (λ a f l, cons a (f l))

def flatten {A : Type} : list (list A) → list A :=
fold nil concat 

/- We have now finished defining our basic operations on lists. Let us check by some examples 
   that the operations indeed do what they are supposed to do. With your mouse, hover over the
   #reduce keyword to see what each term reduces to. -/

#reduce concat (cons 1 (cons 2 (cons 3 nil))) (cons 4 (cons 5 nil))

#reduce sum_list_ℕ (concat (cons 1 (cons 2 (cons 3 nil))) (cons 4 (cons 5 nil)))

#reduce  flatten (cons (cons 1 (cons 2 nil)) (cons (cons 3 nil) (cons (cons 4 (cons 5 nil)) nil)))

/- Of course, if you really want to know that your operations behave as expected, you should 
   prove the relevant properties about them. This is what we will do next. -/

/- When proving theorems, we can also proceed by pattern matching. In a pattern matching argument
   we can recursively call the object we are defining on earlier instances.
   
   The arguments that we want to pattern-match on, must appear after the colon (:) in the 
   specification of the theorem. -/

theorem map_id {A : Type} :
    ∀ (x : list A), map id x = x 
| nil := rfl
| (cons a x) := 
    calc
    map id (cons a x) 
        = cons a (map id x) : rfl
    ... = cons a x : by rw map_id

theorem map_composition {A : Type} {B : Type} {C : Type} (f : A → B) (g : B → C) :
    ∀ (x : list A), map (g ∘ f) x = map g (map f x)
| nil := rfl
| (cons a x) := 
    calc
    map (g ∘ f) (cons a x)
        = cons (g (f a)) (map (g ∘ f) x) : rfl 
    ... = cons (g (f a)) (map g (map f x)) : by rw map_composition
    ... = map g (map f (cons a x)) : rfl   

/- Next, we prove some properties concatenation. Concatenation of lists is an associative
   operation, and it satisfies the left and right unit laws.universe
   
   In order to prove associativity, we note that since concatenation is defined by induction
   on the left argument, we will again use induction on the left argument to prove this 
   propoerty. The proof is presented by pattern matching.
   
   In the proof we will use the built-in equation compiler. We just calculate as if we were
   working on a sheet of paper, and each time we mention the reason why the equality holds. -/

theorem assoc_concat {A : Type} : 
    ∀ (x y z : list A), concat (concat x y) z = concat x (concat y z)
| nil _ _ := rfl
| (cons a l) y z :=
    calc
    concat (concat (cons a l) y) z 
        = cons a (concat (concat l y) z) : by reflexivity
    ... = cons a (concat l (concat y z)) : by rw assoc_concat
    ... = concat (cons a l) (concat y z) : by reflexivity

theorem left_unit_concat {A : Type} : 
    ∀ (x : list A), concat nil x = x := 
    eq.refl 

theorem right_unit_concat {A : Type} : 
    ∀ (x : list A), concat x nil = x 
| nil := rfl
| (cons a x) := 
    show cons a (concat x nil) = cons a x, 
    by rw right_unit_concat 

/- Next, we prove the elementary properties of the length function. -/

theorem length_nil {A : Type} :
    length (@nil A) = 0 := rfl

theorem length_unit {A : Type} (a : A) :
    length (unit a) = 1 := rfl

theorem length_concat {A : Type} :
    ∀ (x y : list A), length (concat x y) = length x + length y
| nil y := 
    calc
    length (concat nil y) 
        = length y : rfl
    ... = 0 + length y : by rw nat.zero_add
    ... = length nil + length y : by rw length_nil
| (cons a x) y :=
    calc
    length (concat (cons a x) y)
        = length (concat x y) + 1 : rfl
    ... = (length x + length y) + 1 : by rw length_concat
    ... = (length x + 1) + length y : by rw nat.succ_add
    ... = (length (cons a x)) + length y : rfl

/- Next, we prove the elemenatary properties of the flatten function. -/

theorem flatten_unit {A : Type} :
    ∀ (x : list A), flatten (unit x) = x := 
    right_unit_concat

theorem flatten_map_unit {A : Type} : 
    forall (x : list A), flatten (map unit x) = x
| nil := rfl 
| (cons a x) := 
    calc
    flatten (map unit (cons a x))
        = cons a (flatten (map unit x)) : rfl
    ... = cons a x : by rw flatten_map_unit

-- flatten a list of units.

theorem length_flatten {A : Type} :
    ∀ (x : list (list A)), length (flatten x) = sum_list_ℕ (map length x)
| nil := rfl
| (cons a x) := 
    calc
    length (flatten (cons a x)) 
        = length (concat a (flatten x)) : rfl
    ... = length a + length (flatten x) : by rw length_concat 
    ... = length a + sum_list_ℕ (map length x) : by rw length_flatten 
    ... = sum_list_ℕ (map length (cons a x)) : rfl 

theorem flatten_concat {A : Type} :
    ∀ (x y : list (list A)), flatten (concat x y) = concat (flatten x) (flatten y)
| nil y := rfl
| (cons a x) y := 
    calc
    flatten (concat (cons a x) y) 
        = concat a (flatten (concat x y)) : rfl
    ... = concat a (concat (flatten x) (flatten y)) : by rw flatten_concat
    ... = concat (concat a (flatten x)) (flatten y) : by rw assoc_concat
    ... = concat (flatten (cons a x)) (flatten y) : rfl 

theorem flatten_flatten {A : Type} :
    ∀ (x : list (list (list A))), flatten (flatten x) = flatten (map flatten x)
| nil := rfl
| (cons a x) := 
    calc
    flatten (flatten (cons a x))
        = flatten (concat a (flatten x)) : rfl
    ... = concat (flatten a) (flatten (flatten x)) : by rw flatten_concat
    ... = concat (flatten a) (flatten (map flatten x)) : by rw flatten_flatten 
    ... = flatten (map flatten (cons a x)) : rfl 

/- This concludes our coverage of lists in Lean. -/

end list 

/- Next, we study lists of a fixed length. They are a natural example of a dependent type.-/

inductive vector (A : Type) : ℕ → Type 
| nil : vector 0
| cons : ∀ {n : ℕ}, A → vector n → vector (n+1)

namespace vector

def map {A : Type} {B : Type} (f : A → B) :
    ∀ {n : ℕ}, vector A n → vector B n 
| 0 nil := nil
| (n+1) (cons a x) := cons (f a) (map x)

def head {A : Type} :
    ∀ {n : ℕ}, vector A (n+1) → A 
| n (cons a x) := a 

def tail {A : Type} : 
    ∀ {n : ℕ}, vector A (n+1) → vector A n 
| n (cons a x) := x 

def concat {A : Type} :
    ∀ {m n : ℕ}, vector A m → vector A n → vector A (m+n)
| 0 n nil y := 
    begin
    rw nat.zero_add,
    exact y,
    end
| (m+1) n (cons a x) y := 
    begin
    rw nat.succ_add,
    exact cons a (concat x y),
    end

/- Using lists of fixed length, we can define matrices. The type
   Matrix m n A is the type of matrices with m rows and n columns
   and with coefficients in A. -/

def Matrix (m n : ℕ) (A : Type) : Type :=
vector (vector A n) m

def top_row {A : Type} {m n : ℕ} : 
    Matrix (m+1) n A → vector A n := 
head 

def tail_vertical {A : Type} {m n : ℕ} : 
    Matrix (m+1) n A → Matrix m n A :=
tail 

def left_column {A : Type} {m n : ℕ} :
    Matrix m (n+1) A → vector A m := 
map head

def tail_horizontal {A : Type} {m n : ℕ} : 
    Matrix m (n+1) A → Matrix m n A :=
map tail

/- Since matrices are rectangular, we have a horizontal as well as vertical empty matrices. -/

def nil_vertical {A : Type} {n : ℕ} : Matrix 0 n A := nil

theorem eq_nil_vertical {A : Type} : 
    ∀ {n : ℕ} (x : Matrix 0 n A), x = nil_vertical
| 0 nil := rfl 
| (n+1) nil := rfl  

def nil_horizontal {A : Type} : ∀ {m : ℕ}, Matrix m 0 A 
| 0 := nil 
| (m+1) := cons nil nil_horizontal

theorem eq_nil_horizontal {A : Type} : 
    ∀ {m : ℕ} (x : Matrix m 0 A), x = nil_horizontal
| 0 nil := rfl 
| (m+1) (cons nil M) := 
    calc
    cons nil M 
        = cons nil nil_horizontal : by rw eq_nil_horizontal M  
    ... = nil_horizontal : rfl

/- Similarly, there is a horizontal cons and a vertical cons. -/

/- cons_vertical adds a new row from the top. -/

def cons_vertical {A : Type} {m n : ℕ} :
    vector A n → Matrix m n A → Matrix (m+1) n A :=
cons

/- cons_horizontal adds a new column from the left. -/

def cons_horizontal {A : Type} :
    ∀ {m n : ℕ}, vector A m → Matrix m n A → Matrix m (n+1) A 
| 0 n nil M := nil
| (m+1) n (cons a x) M := 
    cons (cons a (top_row M)) (cons_horizontal x (tail_vertical M))

/- We define the transposition of a matrix. -/

def transpose {A : Type} : 
    ∀ {m n : ℕ}, Matrix m n A → Matrix n m A
| 0 n M := nil_horizontal
| (m+1) n (cons x M) := cons_horizontal x (transpose M)

/- The following two theorems show how transpose interacts with the basic operations on
   matrices. These will help to show that transposition is an involution. -/

theorem transpose_cons_horizontal {A : Type} :
    ∀ {m n : ℕ} (x : vector A m) (M : Matrix m n A),
    transpose (cons_horizontal x M) = cons_vertical x (transpose M)
| 0 n nil M := rfl 
| (m+1) n (cons a x) (cons y M) := 
    calc
    transpose (cons_horizontal (cons a x) (cons y M))
        = transpose (cons (cons a y) (cons_horizontal x M)) : rfl 
    ... = cons_horizontal (cons a y) (transpose (cons_horizontal x M)) : rfl 
    ... = cons_horizontal (cons a y) (cons_vertical x (transpose M)) : by rw transpose_cons_horizontal
    ... = cons_vertical (cons a x) (transpose (cons y M)) : by reflexivity

theorem transpose_cons_vertical {A : Type} :
    ∀ {m n : ℕ} (x : vector A n) (M : Matrix m n A),
    transpose (cons_vertical x M) = cons_horizontal x (transpose M)
| m n x M := rfl 

/- We finally show that transposition is an involution. -/

theorem transpose_transpose {A : Type} :
    ∀ {m n : ℕ} (M : Matrix m n A), transpose (transpose M) = M
| 0 0 nil := rfl
| 0 (n+1) nil := rfl 
| (m+1) 0 M := 
    calc
    transpose (transpose M) 
        = nil_horizontal : rfl
    ... = M : by rw eq_nil_horizontal M
| (m+1) (n+1) (cons x M) := 
    calc
    transpose (transpose (cons x M))
        = transpose (cons_horizontal x (transpose M)) : rfl
    ... = cons_vertical x (transpose (transpose M)) : by rw transpose_cons_horizontal
    ... = cons_vertical x M : by rw transpose_transpose
    ... = cons x M : rfl

end vector

end logika_v_racunalnistvu