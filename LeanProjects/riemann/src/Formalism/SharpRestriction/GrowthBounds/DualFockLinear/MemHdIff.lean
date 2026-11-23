import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosDef

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def TE (K : Type) [CommRing K] (k : ℕ) (vec : Bool) (d : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  if vec then X a * pderiv b f else (if a = b then (d : K) • f else 0) - X b * pderiv a f

def RestAdj : Prop :=
  ∀ (K : Type) [Field K] (k : ℕ) (a b : Fin k) (P Q : MvPolynomial (Fin k × Fin k) K),
    fockR (RE K k a b P) Q = fockR P (RE K k b a Q)

def RestStab : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (ν : Fin k → ℕ) (a b : Fin k), ∀ P ∈ dualWeyl K k k ν, RE K k a b P ∈ dualWeyl K k k ν

def RestTheta : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)), ∀ P ∈ Hd K (m + 1) d,
    RE K (m + 1) a b (theta K m vec P) = theta K m vec (TE K (m + 1) vec d a b P)

def RestWt : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∃ (J : Type) (b : J → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (μ : J → Fin (m + 1) → ℕ),
      Submodule.span K (Set.range b) = dualWeyl K (m + 1) (m + 1) ν ∧
      (∀ i a, RE K (m + 1) a a (b i) = (μ i a : K) • b i) ∧ ∀ i a, μ i a ≤ ν 0

def RestRep : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d : ℕ),
    (∀ P ∈ Hd K (m + 1) d, (∀ Q ∈ Hd K (m + 1) d, fockR (theta K m vec P) (theta K m vec Q) = 0) → P = 0)

theorem RE_mul (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f * g) = RE K k a b f * g + f * RE K k a b g := by
  unfold RE
  simp only [MvPolynomial.pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun t _ => ?_ <;> ring

theorem RE_add (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f + g) = RE K k a b f + RE K k a b g := by
  unfold RE
  simp only [map_add, mul_add, Finset.sum_add_distrib]

theorem mem_Hd_iff {K : Type} [CommRing K] {k d : ℕ} (P : MvPolynomial (Fin k) K) :
    P ∈ Hd K k d ↔ P ∈ homogeneousSubmodule (Fin k) K d := by
  rw [Formalism.L2.G.Model.mem_Hd, mem_homogeneousSubmodule]
  constructor
  · intro h μ hμ
    have := h μ (mem_support_iff.2 hμ)
    rw [← this]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  · intro h μ hμ
    have := h (mem_support_iff.1 hμ)
    rw [← this]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]

theorem EdWord_coe (K : Type) [Field K] (k d : ℕ) (l : List (Fin k × Fin k)) (P : ↥(homogeneousSubmodule (Fin k) K d)) :
    ((EdWord K k d l P : ↥(homogeneousSubmodule (Fin k) K d)) : MvPolynomial (Fin k) K) =
      word1 l (P : MvPolynomial (Fin k) K) := by
  induction l with
  | nil => simp [EdWord, word1]
  | cons y l ih =>
    have : EdWord K k d (y :: l) = Ed K k d y.1 y.2 * EdWord K k d l := by simp [EdWord]
    rw [this, Module.End.mul_apply]
    show X y.1 * pderiv y.2 ((EdWord K k d l P : ↥(homogeneousSubmodule (Fin k) K d)) : MvPolynomial (Fin k) K) = _
    rw [ih]
    rfl

end Formalism.MainNotions.TestSideCounting
