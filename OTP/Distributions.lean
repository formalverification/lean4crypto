import Mathlib.Probability.Distributions.Uniform  -- for uniformOfFintype
import OTP.Basic                                  -- for Key, Plaintext, etc.

/-! # OTP.Distributions.lean

This file defines the probability distributions related to the one-time pad (OTP) cryptographic scheme.
It includes:

- Uniform distribution over keys
- Joint distribution of plaintext and key
- Ciphertext distribution derived from plaintext and key
- Conditional distribution of ciphertext given plaintext

Files in this series:

- OTP.Basic: Basic definitions and operations for OTP
- OTP.KeyUniqueness: Properties of keys in OTP
- OTP.Distributions: Probability distributions related to OTP
- OTP.PerfectSecrecy: Properties of perfect secrecy in OTP
- OTP.Examples: Concrete examples and demos of OTP operations and properties
- OTP.SimpleSecrecy: Simplified version of OTP.PerfectSecrecy where we assume
                      the message distribution is uniform.
-/


-- Ensure Fintype and Nonempty instances are available for:
-- Ciphertext n, Key n (needed for uniformOfFintype, etc.)
instance key_fintype {n : ℕ} : Fintype (Key n) := by
  unfold Key; exact inferInstance
instance key_nonempty {n : ℕ} : Nonempty (Key n) := by
  unfold Key; exact inferInstance


/-! ## Uniform Key Distribution -/

-- Define a uniform PMF over keys of length n.
noncomputable def μK {n : ℕ} : PMF (Key n) := PMF.uniformOfFintype (Key n)
-- `PMF.uniformOfFintype` is noncomputable because it involves division to
-- compute probabilities (which are `NNReal`, non-negative reals).

-- card (Key n) is 2^n. Mathlib has `card_vector`.
-- `card (List.Vector Bool n) = (card Bool) ^ n = 2 ^ n`.
-- So, (μK k) should be (1 / (2^n : ℝ≥0)). (NNReal for probabilities)
#check μK (n := 3) -- PMF (Key 3)
#check μK (n := 3) ⟨[true, false, true], rfl⟩

-- This is a PMF with probabilities 1/8 for each key

-- We can verify properties later, e.g.,
-- `(μK k) = 1 / card (Key n)`

/-! ## Independence and Joint Distribution

  The crucial assumption for OTP's perfect secrecy is that the key
  is chosen independently of the message.

  For pmfs `μM : PMF (Plaintext n)` and `μK : PMF (Key n)`, their joint
  distribution `μMK : PMF (Plaintext n × Key n)` assigns probability
  `(μM m) ⬝ (μK k)` to the pair `(m, k)`.
 -/
noncomputable def
  μMK {n : ℕ} (μM : PMF (Plaintext n)) : PMF (Plaintext n × Key n) :=
    PMF.bind μM (λ m => PMF.map (λ k => (m, k)) μK)

/-! ## Ciphertext Distribution -/

-- Define ciphertext distribution by applying `encrypt` to each message-key pair.
noncomputable def
  μC {n : Nat} (μM : PMF (Plaintext n)) : PMF (Ciphertext n) :=
    PMF.bind (μMK μM) (λ ⟨m, k⟩ => PMF.pure (encrypt m k))
  -- or, PMF.map (λ ⟨m, k⟩ => encrypt m k) (μMK μM)

/-! ## ℙ(C = c | M = m)

  This represents the probability of observing ciphertext `c`, given
  the message is `M = m`.

  If the message is `m`, the ciphertext r.v. `C = encrypt(m, K)` depends
  only on the randomly chosen key (which follows the `μK` distribution).
-/
noncomputable def
  μC_M {n : Nat} (m : Plaintext n) : PMF (Ciphertext n) :=
    PMF.bind μK (λ k => PMF.pure (encrypt m k))
    -- or PMF.map (λ k : Key n => encrypt m k) μK
