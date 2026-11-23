import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem centralChar_subquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL k, ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL k) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  intro k _ _ _ _
  refine ⟨fun y => ?_, fun t m x hd ω hω τ ω' hsub hω' => ?_⟩
  · obtain ⟨f, _, hf⟩ := LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
    exact ⟨f, hf⟩
  · have hcen : HasCentralChar (prodIrr x hd) (∏ a, ω a) :=
      CentralSupport.hasCentralChar_multiProd_prod _ (fun a => (x a).rep) ω hω
    have := Model.nontrivial_of_isIrreducible τ.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : τ.V)
    ext z
    have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
    rw [hω'] at h1
    exact smul_left_injective ℂ hv h1

end GlobalTheory.GamMul
