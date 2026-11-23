import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine mcPts)

noncomputable section

instance isPrime_span_prime (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).2 (Nat.prime_iff_prime_int.1 p.2)

abbrev ZP (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})

instance (p : Nat.Primes) : IsDiscreteValuationRing (ZP p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (P := Ideal.span {((p : ℕ) : ℤ)})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero) (ZP p)

variable {K : Type} {ι : K → Type} {σ : Type}

def extTo (R : Type) [CommRing R] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) : Ideal (MvPolynomial (Σ k, ι k) R) :=
  P.map (MvPolynomial.map (Int.castRingHom R))

def LocPair.IsVertOff [DecidableEq K] (T : LocPair ι ℤ σ) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ))
    (S : Finset Nat.Primes) : Prop :=
  ∀ i, (∃ bf bg : K → ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (T.f i) bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (T.g i) bg ∧
      (fun k => (bf k : ℤ) - bg k) = T.x i - T.x' i) ∧ T.f i ∉ P ∧ T.g i ∉ P ∧
    ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * T.f i - v * T.g i ∈ P

def LocPair.linNum [Fintype σ] {R : Type} [CommRing R] (T : LocPair ι R σ) (la : σ → ℤ) :
    MvPolynomial (Σ k, ι k) R :=
  ∏ i, T.f i ^ (la i).toNat * T.g i ^ (-la i).toNat

def LocPair.linDen [Fintype σ] {R : Type} [CommRing R] (T : LocPair ι R σ) (la : σ → ℤ) :
    MvPolynomial (Σ k, ι k) R :=
  ∏ i, T.g i ^ (la i).toNat * T.f i ^ (-la i).toNat

def LocPair.lin [Fintype σ] {R : Type} [CommRing R] (T : LocPair ι R σ) (la : σ → ℤ) : LocPair ι R Unit :=
  ⟨fun _ => ∑ i, la i • T.x i, fun _ => ∑ i, la i • T.x' i, fun _ => T.linNum la, fun _ => T.linDen la⟩

variable [Fintype K]

def LocPair.IsIsometric (T : LocPair ι ℤ σ) (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A A' : σ → HermLine ι) :
    Prop :=
  ∀ i, (A i).a = T.x i ∧ (A' i).a = T.x' i ∧ ∀ z ∈ mcPts P,
    ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f i))‖ * (A' i).h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g i))‖ * (A i).h z

def arList (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (l : List (HermLine ι)) : ℝ :=
  I P l.length l.get

def arNum (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι) (H : MvPolynomial σ ℝ) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * arList I P (μ.toMultiset.map A).toList

def HasConstants (R A : Type) [CommRing R] [CommRing A] {Ω : Type} [Field Ω] [Algebra R Ω] [Algebra A Ω]
    (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c, GroundTheory.Heights₂.Heights.NumbersDVR.segreVec y c ≠ 0 → ∀ a : A,
    algebraMap A Ω a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing R (GroundTheory.Heights₂.Heights.NumbersDVR.segreVec y) c

end

end GlobalTheory.CompanionTheory.Ar.Num
