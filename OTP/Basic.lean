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


-- Demo 1: Basic OTP Operations ----------------------------------
-- Examples using List literals for the List.Vector constructor

  -- Create a 4-bit message
  def demo_msg : Plaintext 4 := ⟨[true, false, true, true], by decide⟩
  def demo_key : Key 4 := ⟨[false, true, false, true], by decide⟩

  -- Show encryption
  #eval encrypt demo_msg demo_key
  -- Output: [true, true, true, false]

  -- Show decryption recovers the message
  #eval decrypt (encrypt demo_msg demo_key) demo_key
  -- Output: [true, false, true, true]

  -- Show that different keys give different ciphertexts
  def demo_key2 : Key 4 := ⟨[true, true, false, false], by decide⟩
  #eval encrypt demo_msg demo_key2
  -- Output: [false, true, true, true]

-----------------------------------------------------------------

-- Formalization of OTP properties

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
      -- New Goal: `xor (get (map₂ xor m k) i) (get k i) = get m i`
    simp -- This is exactly `(m i xor k i) xor k i = m i`
         -- `simp` recognizes this and proves equality.

----------------------------------------------------------------
-- Demo 2: XOR Properties
-- Some useful lemmas about Boolean xor

  -- Interactive proof that XOR is self-inverse
  example (a b : Bool) : xor (xor a b) b = a := by
    -- Let's explore the proof interactively
    rw [xor_assoc]
    -- Goal: xor a (xor b b) = a
    rw [Bool.xor_self]
    -- Goal: xor a false = a
    rw [Bool.xor_false]
    -- Done!

  -- Another way using simp
  example (a b : Bool) : xor (xor a b) b = a := by simp

----------------------------------------------------------------

-- Let's give these examples names so we can refer to them later.
  lemma xor_abb_eq_a (a b : Bool) : xor (xor a b) b = a := by
    rw [xor_assoc a b b] -- a xor (b xor b)
    rw [Bool.xor_self b] -- a xor false
    rw [xor_false a]     -- a

  lemma xor_aab_eq_b (a b : Bool) : xor a (xor a b) = b := by
    rw [← xor_assoc a a b] -- (a xor a) xor b
    rw [Bool.xor_self a]   -- false xor b
    rw [false_xor b]       -- b

  -- Lemma: a xor b = c ↔ b = a xor c
  lemma xor_ab_eq_c_iff_b_eq_ac (a b c : Bool) : xor a b = c ↔ b = xor a c := by
    constructor -- Splits the goal into two implications (↔)

    -- Part 1: Forward direction (xor a b = c → b = xor a c)
    · intro h_ab_eq_c -- Assume xor a b = c
                      -- We need to show b = xor a c.
    -- To show equality of two Booleans, show their XOR is false.
    -- Goal: b xor (xor a c) = false
      rw [← h_ab_eq_c]      -- New Goal: b xor (xor a (xor a b)) = false
      rw [xor_aab_eq_b a b] -- New Goal: is b xor b = false

    -- Part 2: Backward direction (b = xor a c → xor a b = c)
    · intro h_b_eq_ac -- Assume b = xor a c
                      -- We need to show xor a b = c.
    -- Substitute b using h_b_eq_ac:
      rw [h_b_eq_ac]          -- New Goal: xor a (xor a c) = c
      rw [xor_aab_eq_b a c]   -- New Goal: c = c, which is rfl

  theorem key_uniqueness {n : Nat} (m : Plaintext n) (k : Key n) (c : Ciphertext n) :
    vec_xor m k = c ↔ k = vec_xor m c := by
    constructor -- Splits the goal into two implications (↔)

    -- Part 1: Forward direction (vec_xor m k = c → k = vec_xor m c)
    · intro h_vmk_eq_c -- Assume vec_xor m k = c
                       -- We need to show k = vec_xor m c.

      -- To show equality of two vectors, we show their elements are equal.
      apply ext  -- New Goal: for an arbitrary element i,
      intro i    --           get k i = get (vec_xor m c) i
      simp only [vec_xor, get_map₂] -- Simplify RHS: get k i = xor (get m i) (get c i)
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
