import Mathlib.Data.Vector.Basic

namespace OTP
  open List.Vector
  open Bool
  -- Define types using List.Vector
  def Plaintext  (n : Nat) := List.Vector Bool n
  def Key        (n : Nat) := List.Vector Bool n
  def Ciphertext (n : Nat) := List.Vector Bool n

  -- Element-wise XOR for List.Vector
  def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) := map₂ xor v₁ v₂

  def encrypt {n : Nat} (m : Plaintext n) (k : Key n) : Ciphertext n :=
    vec_xor m k

  def decrypt {n : Nat} (c : Ciphertext n) (k : Key n) : Plaintext n :=
    vec_xor c k

  -- Examples using List literals for the List.Vector constructor
  def ex_p : Plaintext 3 := ⟨[true, false, true], by decide⟩
  def ex_k : Key 3 := ⟨[false, true, true], by rfl⟩ -- rfl is fine if decide is slow

  #eval encrypt ex_p ex_k -- Should output: [true, true, false]
  #eval decrypt (encrypt ex_p ex_k) ex_k -- Should output: [true, false, true]

  lemma encrypt_decrypt {n : Nat} (m : Plaintext n) (k : Key n) :
    decrypt (encrypt m k) k = m := by
    -- Step 1: unfold definitions
    unfold encrypt decrypt vec_xor
    -- After unfolding, goal is `map₂ xor (map₂ xor m k) k = m`

    -- Step 2: apply vector extensionality
    apply ext -- changes goal from vector equality to element-wise equality.
    intro i   -- new goal: ∀ (i : Fin n), ((m xor k) xor k) i = m i

    -- Step 3: Simplify the per-element equality
    simp only [get_map₂]
      -- get_map₂ (f : α → β → γ) (v₁ : List.Vector α n)
      --          (v₂ : List.Vector β n) (i : Fin n) :
      --          (map₂ f v₁ v₂).get i = f (v₁.get i) (v₂.get i)
      -- So goal becomes: `xor (get (map₂ xor m k) i) (get k i) = get m i`
    simp -- using `get_map₂` on the outer `map₂`
    -- `get (map₂ xor (map₂ xor m k) k) i = get m i` becomes
    -- `xor (get (map₂ xor m k) i) (get k i) = get m i`
    -- using `get_map₂` on the inner `map₂`, this becomes
    -- `xor (xor (get m i) (get k i)) (get k i) = get m i`
    -- This is exactly `(x xor y) xor y = x` where `x` is `(get m i)`
    -- and `y` is `(get k i)`. `simp` recognizes this and proves equality.

  -- The a xor (a xor b) = b lemma
  lemma xor_aab_eq_b (a b : Bool) : xor a (xor a b) = b := by
    rw [← xor_assoc a a b] -- (a xor a) xor b
    rw [Bool.xor_self a]   -- false xor b
    rw [false_xor b]       -- b

  -- The (a xor b) xor b = a lemma
  lemma xor_abb_eq_a (a b : Bool) : xor (xor a b) b = a := by
    rw [xor_assoc a b b] -- a xor (b xor b)
    rw [Bool.xor_self b] -- a xor false
    rw [xor_false a]     -- a

  -- The a xor b = c ↔ b = a xor c
  lemma xor_ab_eq_c_iff_b_eq_ac (a b c : Bool) : xor a b = c ↔ b = xor a c := by
    constructor -- Splits the goal into two implications (↔)
    -- Part 1: Forward direction (xor a b = c → b = xor a c)
    · intro h_ab_eq_c -- Assume xor a b = c
    -- We need to show b = xor a c.
    -- To show equality of two Booleans, we can show their XOR is false.
    -- Goal: b xor (xor a c) = false
      rw [← h_ab_eq_c] -- Now goal is b xor (xor a (xor a b)) = false
      rw [xor_aab_eq_b a b] -- Now goal is b xor b = false
    -- Part 2: Backward direction (b = xor a c → xor a b = c)
    · intro h_b_eq_ac -- Assume b = xor a c
    -- We need to show xor a b = c.
    -- Substitute b using h_b_eq_ac:
      rw [h_b_eq_ac] -- Now goal is xor a (xor a c) = c
    -- Goal is now: xor a (xor a c) = c
      rw [xor_aab_eq_b a c] -- Now goal is c = c, which is rfl

  theorem key_uniqueness {n : Nat} (m : Plaintext n) (k : Key n) (c : Ciphertext n) :
    vec_xor m k = c ↔ k = vec_xor m c := by
    constructor -- Splits the goal into two implications (↔)

    -- Part 1: Forward direction (vec_xor m k = c → k = vec_xor m c)
    · intro h_vmk_eq_c -- Assume vec_xor m k = c
      -- We need to show k = vec_xor m c.
      -- To show equality of two vectors, we show their elements are equal.
      apply ext  -- goal is now, for an arbitrary element i,
      intro i    -- get k i = get (vec_xor m c) i
      simp only [vec_xor, get_map₂] -- Simplify RHS: get k i = Bool.xor (get m i) (get c i)
      apply (xor_ab_eq_c_iff_b_eq_ac (get m i) (get k i) (get c i)).mp

      -- Now use hypothesis h_vmk_eq_c: `vec_xor m k = c`.
      -- Apply `get _ i` to both sides: `get (vec_xor m k) i = get c i`
      rw [← congr_arg (λ v => get v i) h_vmk_eq_c]
      -- New Goal: `xor (get m i) (get k i) = (vec_xor m k).get i`
      simp only [vec_xor, get_map₂] -- Simplifies RHS to `xor (get m i) (get k i)`

    -- Part 2: Backward direction (k = vec_xor m c → vec_xor m k = c)
    · intro h_k_eq_vmc -- Assume k = vec_xor m c
      show vec_xor m k = c
      -- Substitute k using h_k_eq_vmc:
      rw [h_k_eq_vmc] -- New Goal: vec_xor m (vec_xor m c) = c
      -- This is the vector equivalent of `a xor (a xor b) = b`.
      -- Prove by extensionality:
      ext i  -- New Goal: get (vec_xor m (vec_xor m c)) i = get c i
      simp only [vec_xor, get_map₂] -- Apply get_map₂ twice on the LHS
      -- New Goal: xor (get m i) (xor (get m i) (get c i)) = get c i
      -- This holds by the `a xor (a xor b) = b` lemma:
      apply xor_aab_eq_b (get m i) (get c i)

end OTP
