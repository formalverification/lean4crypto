import OTP.Basic
import OTP.KeyUniqueness
import OTP.Distributions

/-! # OTP.PerfectSecrecy.lean

This file proves properties of perfect secrecy in the one-time pad (OTP) cryptographic scheme.
It includes:

- The definition of perfect secrecy
- The proof that OTP achieves perfect secrecy
- The relationship between the key and ciphertext distributions
- The uniformity of the ciphertext distribution given a message
- The uniformity of the ciphertext distribution overall
- The law of total probability for the ciphertext distribution

Files in this series:

- OTP.Basic: Basic definitions and operations for OTP
- OTP.KeyUniqueness: Properties of keys in OTP
- OTP.Distributions: Probability distributions related to OTP
- OTP.PerfectSecrecy: Properties of perfect secrecy in OTP
- OTP.Examples: Concrete examples and demos of OTP operations and properties
- OTP.SimpleSecrecy: Simplified version of OTP.PerfectSecrecy where we assume
                      the message distribution is uniform.

-/
open Classical -- needed for division and ENNReal properties
open Fintype

/-! ### A brief note about coercions
Coercion is a mechanism to convert a term of one type to another to prevent a type error.

For instance, given `n : ℕ` and a function that expects an integer `f (x : ℤ)`, you can
explicitly write `f ↑n` to show the coercion from `ℕ` to `ℤ`.

As far as I can tell, `↑a` signifies coercion of "standard" types, while `⇑e` signifies
coercion of more complicated types.

To type the coercion symbol in the VSCode editor with the Lean4 extension,

* For `↑`, type `\u` or `\uparrow` followed by a space or tab.

* For `⇑`, type `\u=` or `\Uparrow` followed by a space or tab.

You can discover all available Unicode symbol abbreviations within VSCode by
opening the Command Palette (`Ctrl+Shift+P` or `Cmd+Shift+P` on Mac) and
searching for "**Lean 4: Show Unicode Input Abbreviations**".
-/
variable (a : NNReal) (b : ENNReal)
#check a = b -- ↑ coerces a to ENNReal

variable (e : NNReal ≃ ENNReal)
#check ⇑e -- ⇑e : NNReal → ENNReal

/-! ### A brief note about universe levels
Types form a hierarchy that is parameterized by universe levels.  The assertion
that `α` is a type at universe level `ℓ` is expressed as `α : Type ℓ`. Fortunately,
in most cases we can elide this technicality by declaring our types with the
special Lean syntax `α : Type*`, which tells Lean to select a fresh universe level
for `α` and make that level an implicit parameter.
-/


/-! ## LEMMA 1.  Mapping a uniform PMF through a bijection is uniform
This lemma involves proving that two PMFs are equal.  How is this done?
Let's look at the definition of `PMF` in
`mathlib/Mathlib/Probability/ProbabilityMassFunction/Basic.lean`.

```lean
definition of PMF:

def PMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }

namespace PMF

instance instFunLike : FunLike (PMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h

@[ext]
protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h
```

There is an instance of `FunLike` for `PMF α`, which means that we
can treat a PMF as a function from `α` to `ℝ≥0∞`.  This is crucial for
proving that two PMFs are equal: we can show that they assign the same
probability to each possible value of the random variable. Indeed, the
`ext` theorem for `PMF` is essentially function extensionality for PMFs.
-/

lemma map_uniformOfFintype_equiv
    {α : Type*} [Fintype α] [Nonempty α]
    {β : Type*} [Fintype β] [Nonempty β]
    (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  -- Equality of PMFs is proved by showing that they assign the same probability
  -- to each possible value of the random variable.

  ext b
  -- Goal: (PMF.map e (uniformOfFintype α)) b = (uniformOfFintype β) b

  -- Step 1: Simplify the LHS using PMF.map_apply
  rw [PMF.map_apply]
  -- Goal: ∑' (a : α), if b = e a then (uniformOfFintype α) a else 0
  --         = (PMF.uniformOfFintype β) b

  -- Step 2: Apply definition of uniform distribution to both sides
  simp only [PMF.uniformOfFintype_apply]
  -- Goal: ∑' (a : α), if b = e a then (↑(card α))⁻¹ else 0 = (↑(card β))⁻¹

  -- Step 3: The sum has exactly one non-zero term when a = e.symm b
  -- We can rewrite this as a sum over the singleton {e.symm b}
  have h_equiv : (∑' (a : α), if b = e a then (↑(card α : ENNReal))⁻¹ else 0) =
                 (∑' (a : α), if a = e.symm b then (↑(card α))⁻¹ else 0) := by
    congr
    ext a
    -- Goal: (if b = e a then (↑(card α))⁻¹ else 0) = (if a = e.symm b then (↑(card α))⁻¹ else 0)
    by_cases h : b = e a
    · -- Case: b = e a
      rw [if_pos h]
      have h': a = e.symm b := by
        rw [←Equiv.symm_apply_apply e a]
        rw [h]
      rw [if_pos h']
    · -- Case: b ≠ e a
      rw [if_neg h]
      have h' : a ≠ e.symm b := by
        intro contr
        subst contr
        rw [Equiv.apply_symm_apply e] at h
        apply h
        rfl
      rw [if_neg h']

  -- Step 4: Apply the equivalence and simplify
  rw [h_equiv]
  rw [tsum_ite_eq]
  -- Goal: (↑(card α))⁻¹ = (↑(card β))⁻¹

  -- Step 5: Use the fact that equivalent finite types have the same cardinality
  congr 1
  rw [card_congr e]



/-! ## LEMMA 2.  The ciphertext-given-message distribution is uniform -/

-- Ensure Fintype and Nonempty instances are available for:
-- Ciphertext n, Key n (needed for uniformOfFintype)
instance ciphertext_fintype {n : ℕ} : Fintype (Ciphertext n) := by
  unfold Ciphertext; exact inferInstance
instance ciphertext_nonempty {n : ℕ} : Nonempty (Ciphertext n) := by
  unfold Ciphertext; exact inferInstance

lemma C_given_M_eq_inv_card_key {n : ℕ} (m : Plaintext n) (c : Ciphertext n) :
  (μC_M m) c = 1 / card (Key n) := by
  -- `μC_M m = map (encrypt m) μK` and `encrypt m` is the `toFun` of `xorEquiv m`
  have μC_M_def : μC_M m = PMF.map (xorEquiv m).toFun μK := by
    rw [μC_M]
    congr 1
  rw [μC_M_def]
  -- Now goal is (PMF.map (xorEquiv m).toFun μK) c = 1 / card (Key n)
  -- μK is uniformOfFintype (Key n)
  rw [μK] -- replace μK with its definition
  -- Goal: (PMF.map (xorEquiv m).toFun (uniformOfFintype (Key n))) c = 1 / card (Key n)

  -- Apply map_uniformOfFintype_equiv:
  -- map (xorEquiv m).toFun (uniformOfFintype (Key n)) = uniformOfFintype (Ciphertext n)
  have h_map_equiv : PMF.map (xorEquiv m).toFun (PMF.uniformOfFintype (Key n))
    = PMF.uniformOfFintype (Ciphertext n) := by
    exact map_uniformOfFintype_equiv (xorEquiv m)
  rw [h_map_equiv]
  -- Goal: (uniformOfFintype (Ciphertext n)) c = 1 / card (Key n)
  rw [PMF.uniformOfFintype_apply]
  -- Goal: (card (Ciphertext n) : NNReal)⁻¹ = 1 / card (Key n)
  rw [one_div] -- RHS becomes (card (Key n))⁻¹
  -- Goal: (card (Ciphertext n))⁻¹ = (card (Key n))⁻¹
  -- This is true if card (Ciphertext n) = card (Key n)
  rw [card_congr (xorEquiv m)] -- Rewrites card (Ciphertext n) to card (Key n) on LHS


/-! ### Example
    For a 3-bit message and ciphertext, the conditional distribution is uniform:
   `∀ c, P(C = c | M = m) = 1/8`                                                 -/
  example (m : Plaintext 3) (c : Ciphertext 3) :
    (μC_M m) c = 1/8 := by
    rw [C_given_M_eq_inv_card_key]
    -- Goal: 1 / ↑(card (Key 3)) = 1 / 8
    unfold Key
    rw [card_vector]
    -- Goal: 1 / ↑(card Bool ^ 3) = 1 / 8
    simp


-- ENNReal version of Lemma 1.
lemma C_given_M_eq_inv_card_key_ennreal {n : ℕ} (m : Plaintext n) (c : Ciphertext n) :
  (μC_M m) c = (card (Key n) : ENNReal)⁻¹ := by
  -- Use the NNReal version and convert
  rw [C_given_M_eq_inv_card_key m c]
  simp


-- Corollary: The conditional distribution of `C` given `M=m` doesn't depend on `m`.
theorem conditional_independent_of_message {n : Nat}
  (m₁ m₂ : Plaintext n) (c : Ciphertext n) :
  μC_M m₁ c = μC_M m₂ c := by
  rw [C_given_M_eq_inv_card_key_ennreal, C_given_M_eq_inv_card_key_ennreal]


/-! ## LEMMA 2: The overall ciphertext distribution `μC` is also uniform.-----------
The probability `P(C = c)` that ciphertext `c` is observed (which is `(μC μM) c`),
is uniform over the ciphertext space. That is: `(μC μM) c = 1 / (card (Ciphertext n))`

Since `card (Key n) = card (Ciphertext n)` (due to `xorEquiv`), this would imply
that `(μC μM) c` is also equal `1 / card (Key n)`.
-/

/-! ## Law of Total Probability for Discrete Distributions in Lean 4

### REVIEW: Probability in Lean/Mathlib

In Mathlib, discrete probability distributions are represented using the `PMF` (Probability Mass Function) type.
- `PMF α` represents a probability distribution over a type `α`
- For `p : PMF α` and `a : α`, the expression `p a` gives the probability of outcome `a`
- Probabilities are represented as `NNReal` (non-negative real numbers) in [0, ∞)
- When doing arithmetic, we often coerce to `ENNReal` (extended non-negative reals) in [0, ∞]

### REVIEW: Random Variables and Transformations

In probability theory, if X is a random variable with distribution μX, and Y = f(X) for some function f,
then the distribution of Y can be computed using:
- `PMF.map f μX` - the distribution of f(X)
- `PMF.bind μX g` - for dependent distributions, where g : α → PMF β

### REVIEW: The Law of Total Probability

For random variables X and Y, the law of total probability states:
P(Y = y) = Σ_x P(Y = y , X = x) = Σ_x P(Y = y | X = x) P(X = x)

In our case:
- X is the message M with distribution μM
- Y is the ciphertext C with distribution μC
- P(C = c | M = m) is given by μC_M m c
-/

-- Another helper: when we sum (if P then v else 0), we get v if P is true for exactly one element
-- A more robust approach that builds up the proof piece by piece

-- Next, let's establish what PMF.bind actually does.
lemma pmf_bind_expanded {α β : Type*} (p : PMF α) (f : α → PMF β) (b : β) :
  (p.bind f) b = ∑' a, (p a : ENNReal) * (f a b) := by
  -- This is just PMF.bind_apply
  exact PMF.bind_apply _ _ _

/-! ## The Most Basic Statement: P(C = c) = Σ_{m,k} P(C = c ∧ M = m ∧ K = k)  -/

-- Let's prove this in the most direct way possible.

-- The key insight: μC is DEFINED as the distribution you get by:
-- 1. Sampling (m,k) from μMK
-- 2. Outputting encrypt m k
-- So P(C = c) is exactly the sum over all (m,k) where encrypt m k = c

-- This is the definition of marginal probability!
-- By P(C = c) we mean the probability of getting c from the encryption process.
-- The encryption process: sample m, sample k, output encrypt m k
-- So P(C = c) = Σ over all ways to get c = Σ_{m,k : encrypt m k = c} P(M=m)P(K=k)

-- The most direct possible statement
theorem marginal_probability_direct {n : Nat}
  (μM : PMF (Plaintext n)) (c : Ciphertext n) :
  (μC μM) c = ∑' (mk : Plaintext n × Key n),
    if c = encrypt mk.1 mk.2 then ((μMK μM) mk : ENNReal) else 0 := by
  -- This is literally the definition of μC!
  -- μC = bind μMK (λ (m, k) => pure (encrypt m k))
  unfold μC
  rw [PMF.bind_apply (μMK μM) (λ ⟨m, k⟩ => PMF.pure (encrypt m k)) c]
  simp only [PMF.pure_apply]
  simp only [mul_ite, mul_one, mul_zero]

-- That's it! The bind_apply lemma tells us exactly this.
-- PMF.bind_apply says: (p.bind f) y = ∑' x, p x * f x y
-- In our case:
-- - p is μMK μM
-- - f is λ (m, k) => pure (encrypt m k)
-- - y is c
-- And (pure a) b = if b = a then 1 else 0

-- Interpretation:
--   By definition, P(C = c) equals the sum of P(M = m, K = k) over all
--   (m, k) such that encrypt m k = c. This is exactly what μC computes.

/-- The law of total probability for PMFs:
    P(Y = y) = Σ_x P(X = x) * P(Y = y | X = x) -/
-- First, we need the Law of Total Probability for our construction.
theorem law_of_total_probability {n : Nat} (μM : PMF (Plaintext n)) (c : Ciphertext n) :
    (μC μM) c = ∑' m, (μM m : ENNReal) * (μC_M m c) := by
  -- Step 1: Unfold all definitions to get to the fundamental sums.
  simp [μC, μMK, μC_M, PMF.bind_apply, PMF.map_apply]
  -- Goal is a complex equality of summations.

-- A simpler approach that avoids some of the tsum manipulations
lemma prob_C_uniform_ennreal {n : Nat} (μM : PMF (Plaintext n)) (c : Ciphertext n) :
  (μC μM) c = (card (Key n) : ENNReal)⁻¹ := by
  -- Use the fact that we can express μC in terms of conditional probabilities

  rw [law_of_total_probability]

  -- We know that for all m, μC_M m c = (card (Key n))⁻¹
  have h_conditional_uniform : ∀ m : Plaintext n,
    (μC_M m c : ENNReal) = (card (Key n) : ENNReal)⁻¹ := by
    intro m
    exact C_given_M_eq_inv_card_key_ennreal m c

  -- Substitute this uniform value
  simp only [h_conditional_uniform]

  -- Factor out the constant
  rw [ENNReal.tsum_mul_right]

  -- Use that probabilities sum to 1
  rw [PMF.tsum_coe]
  simp

-- Even simpler: directly show that μC is uniform
lemma μC_is_uniform {n : Nat} (μM : PMF (Plaintext n)) :
  μC μM = PMF.uniformOfFintype (Ciphertext n) := by
  -- Two PMFs are equal if they assign the same probability to each element
  ext c
  rw [prob_C_uniform_ennreal, PMF.uniformOfFintype_apply]
  -- Need to show: (card (Key n))⁻¹ = (card (Ciphertext n))⁻¹
  congr 1
  -- This follows from the bijection between Key n and Ciphertext n
  -- (for any fixed message)
  -- exact card_congr (xorEquiv (List.Vector.replicate n false))



/-! ### Perfect Secrecy Theorem ---------------------------------------------
  The theorem states that the probability of a ciphertext given a specific plaintext
  is equal to the probability of that plaintext, which is the essence of perfect secrecy.
  This means that knowing the ciphertext does not give any information about the plaintext.
  The proof uses the uniformity of the ciphertext distribution and the independence of the key.
-/

/-! ### Perfect Secrecy: The Clean Version -/

-- The essence of perfect secrecy: P(C = c | M = m) = P(C = c)
theorem perfect_secrecy_clean {n : Nat} (μM : PMF (Plaintext n))
  (m : Plaintext n) (c : Ciphertext n) :
  (μC_M m c : ENNReal) = (μC μM) c := by
  -- Both sides equal (card (Key n))⁻¹
  rw [C_given_M_eq_inv_card_key_ennreal, prob_C_uniform_ennreal]


-- Interpretation: Observing c tells us nothing about whether m₁ or m₂ was sent
theorem no_information_leakage {n : Nat} (μM : PMF (Plaintext n))
  (m : Plaintext n) (c : Ciphertext n)
  (h_pos : (μC μM) c ≠ 0) :
  -- P(M = m | C = c) = P(M = m)
  (μC_M m c * μM m) / (μC μM) c = μM m := by
  rw [perfect_secrecy_clean]
  rw [mul_comm]
  rw [ENNReal.mul_div_cancel_right h_pos]
  rw [prob_C_uniform_ennreal]           -- Goal: (↑(card (Key n)))⁻¹ ≠ ⊤
  apply ENNReal.inv_ne_top.mpr          -- Goal: ↑(card (Key n)) ≠ 0
  simp only [ne_eq, Nat.cast_eq_zero]   -- Goal: ¬(card (Key n) = 0)
  exact card_ne_zero

-- Summary: both distributions are uniform!
theorem both_distributions_uniform {n : Nat} (μM : PMF (Plaintext n)) :
  (∀ m, μC_M m = PMF.uniformOfFintype (Ciphertext n)) ∧
  (μC μM = PMF.uniformOfFintype (Ciphertext n)) := by
  constructor
  · intro m
    ext c
    rw [C_given_M_eq_inv_card_key, PMF.uniformOfFintype_apply]
    simp
    congr

  · ext c
    rw [prob_C_uniform_ennreal, PMF.uniformOfFintype_apply]
    congr 1




/- ## Classical statement of perfect secrecy theorem -/
theorem perfect_secrecy {n : Nat} (μM : PMF (Plaintext n)) (m₀ : Plaintext n) (c₀ : Ciphertext n) :
  (μC_M m₀) c₀ * μM m₀ / (μC μM) c₀  = μM m₀ := by
    -- Note: (μM m₀) on the RHS is originally NNReal from PMF μM.
    -- It might need to be coerced to ENNReal for the final equality if LHS is ENNReal.
    -- The multiplication and division will likely promote it to ENNReal anyway.

  -- Define local abbreviations with the correct type ENNReal
  -- let P_C_given_M : ENNReal := (μC_M m₀) c₀
  let P_C_given_M := (μC_M m₀) c₀
  -- let P_M_nnreal : ENNReal := μM m₀ -- The original probability P(M=m₀) is NNReal
  -- let P_M : ENNReal := ↑P_M_nnreal -- Coerce P(M=m₀) to ENNReal for arithmetic
  let P_M := μM m₀
  -- let P_C : ENNReal := (μC μM) c₀
  let P_C := (μC μM) c₀

  -- Step 1: Use 'change' to make the goal explicitly use these local ENNReal constants.
  change (P_C_given_M * P_M) / P_C = P_M

  -- Step 2: State what our assumed lemmas (ennreal versions) mean for these.
  have h_P_C_given_M_val : P_C_given_M = (card (Key n) : ENNReal)⁻¹ := by
    exact C_given_M_eq_inv_card_key_ennreal m₀ c₀ -- Use the ENNReal version of your lemma

  have h_P_C_val : P_C = (card (Key n) : ENNReal)⁻¹ := by
    exact prob_C_uniform_ennreal μM c₀ -- Use the ENNReal version of this lemma

  -- Step 3: Rewrite using these facts in the (changed) goal.
  rw [h_P_C_given_M_val, h_P_C_val]
  -- Goal becomes:
  -- (((card (Key n) : ENNReal)⁻¹ * P_M) / (card (Key n) : ENNReal)⁻¹) = P_M

  -- Step 4: Simplify the division using ENNReal properties.
  let N_K_inv_ennreal := (card (Key n) : ENNReal)⁻¹
  -- Goal is now effectively ((N_K_inv_ennreal * P_M) / N_K_inv_ennreal) = P_M

  -- For ENNReal.mul_div_cancel_left_of_ne_zero_of_ne_top, we need:
  -- N_K_inv_ennreal ≠ 0 and N_K_inv_ennreal ≠ ∞
  have h_inv_ne_zero : N_K_inv_ennreal ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    exact ENNReal.natCast_ne_top (card (Key n))

  have h_inv_ne_top : N_K_inv_ennreal ≠ ⊤ := by
    apply ENNReal.inv_ne_top.mpr
    -- We need ↑(card (Key n)) ≠ 0, i.e., card (Key n) ≠ 0
    apply Nat.cast_ne_zero.mpr
    exact card_ne_zero
    -- We need Key n to not be empty. Your `key_nonempty` instance implies this.

  rw [mul_comm N_K_inv_ennreal P_M] -- Changes (X * P_M) to (P_M * X)
  -- Goal: (P_M * N_K_inv_ennreal) / N_K_inv_ennreal = P_M
  -- Now we can apply the cancellation lemma for ENNReal.
  rw [mul_div_assoc P_M N_K_inv_ennreal N_K_inv_ennreal]
  rw [ENNReal.div_self h_inv_ne_zero]
  simp
  apply h_inv_ne_top
