import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumSectionCut
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariantStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousClassSubstitutionStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem divCycle_support_finite {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f : MRing ι O) : (Function.support (divCycle P f)).Finite := by
  haveI : IsNoetherianRing (MRing ι O) := by
    unfold MRing
    infer_instance
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing (MRing ι O) (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra hn
  apply hW
  unfold divCycle
  rw [dif_neg]
  exact fun h => hn h.1

theorem cycList_ratDiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) (l : List (K → ℤ)) :
    cycList (ratDiv P f g) l = cycList (divCycle P f) l - cycList (divCycle P g) l := by
  have e : ratDiv P f g = divCycle P f - divCycle P g := rfl
  unfold cycList
  rw [e]
  exact (cycEval_sub_cycle _ _ _ (divCycle_support_finite P f) (divCycle_support_finite P g)).symm

theorem cycNum_subst_of_add {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (Z : Ideal (MRing ι O) → ℤ) (d : ℕ)
    (hadd : ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d →
      cycList Z ((b + b') :: l) = cycList Z (b :: l) + cycList Z (b' :: l))
    {σ σ' : Type} [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ)
    (hH : H.IsHomogeneous m) (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum Z (fun t => ∑ i, M t i • cls i) H Q =
      cycNum Z cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q :=
  GlobalTheory.T.homogeneous_class_substitution (K → ℤ) d (fun l => (cycList Z l : ℝ))
    (fun l l' h => by rw [GlobalTheory.T.cycle_list_perm_invariant.2 O K ι Z l l' h])
    (fun b b' l h => by rw [hadd b b' l h]; push_cast; rfl)
    σ σ' cls M H m hH Q hQ

theorem cycNum_linear_subst : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a a' f g hf hg hfP hgP σ σ' _ cls M H m hH Q hQ
  have af := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a f hf hfP
  have ag := GlobalTheory.T.divisor_cycle_list_additive O ϖ hϖ K ι P d hP a' g hg hgP
  refine ⟨cycNum_subst_of_add _ d (fun b b' l h => ?_) cls M H m hH Q hQ,
    cycNum_subst_of_add _ d (af · · · ·) cls M H m hH Q hQ⟩
  rw [cycList_ratDiv, cycList_ratDiv, cycList_ratDiv, af b b' l h, ag b b' l h]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
