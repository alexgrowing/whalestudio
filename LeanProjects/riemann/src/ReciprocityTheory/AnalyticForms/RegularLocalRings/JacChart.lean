import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartC

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {n : ℕ}

def ptIdeal (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.eval p : MvPolynomial (Fin n) ℂ →+* ℂ)

instance ptIdeal_isPrime (p : Fin n → ℂ) : (ptIdeal p).IsPrime :=
  RingHom.ker_isPrime _

abbrev locPt (p : Fin n → ℂ) : Type :=
  Localization.AtPrime (ptIdeal p)

abbrev locRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Type :=
  locPt p ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K

def grad (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) : Fin n → ℂ :=
  fun j => eval p (pderiv j h)

def jacSpan (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (grad p '' (K : Set (MvPolynomial (Fin n) ℂ)))

theorem locRing_isLocalRing_isNoetherian (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) : IsLocalRing (locRing K p) ∧ IsNoetherianRing (locRing K p) := by
  have hK : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≤
      IsLocalRing.maximalIdeal (locPt p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro h hh
    have h2 : h ∈ ptIdeal p := (RingHom.mem_ker).2 (hp h hh)
    rw [← Localization.AtPrime.comap_maximalIdeal (I := ptIdeal p)] at h2
    exact h2
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hK
  haveI : Nontrivial (locRing K p) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsNoetherianRing (locPt p) :=
    IsLocalization.isNoetherianRing (ptIdeal p).primeCompl _ inferInstance
  exact ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
    inferInstance⟩

theorem finrank_cotangentSpace_locRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsLocalRing (locRing K p)] :
    Module.finrank (IsLocalRing.ResidueField (locRing K p)) (IsLocalRing.CotangentSpace (locRing K p))
      + Module.finrank ℂ (jacSpan K p) = n := by
  exact @JacobianCriterionAlt.finrank_cot_eq n p K (inferInstanceAs (IsLocalRing (locRing K p)))

theorem exists_jacobian_cut (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e) :
    e ≤ n ∧ ∃ F : Fin (n - e) → MvPolynomial (Fin n) ℂ, (∀ i, F i ∈ K) ∧
      LinearIndependent ℂ (fun i => grad p (F i)) ∧
      ∃ h : MvPolynomial (Fin n) ℂ, eval p h ≠ 0 ∧ ∀ g ∈ K, h * g ∈ Ideal.span (Set.range F) := by
  exact @JacobianCriterionAlt.exists_jacobian_cut' n K p e
    (inferInstanceAs (IsRegularLocalRing (locRing K p))) he

theorem isRegularLocalRing_of_jacobian (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => grad p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locRing K p) ∧ ringKrullDim (locRing K p) = ((n - c : ℕ) : WithBot ℕ∞) := by
  exact JacobianCriterionAlt.isRegularLocalRing_of_jacobian' K p hp F hF hlin hq

end

end ReciprocityTheory.AnForm.R
