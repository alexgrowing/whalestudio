import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
import GroundTheory.AutomorphicForms.WhittakerCriterion

noncomputable section

open GlobalTheory.PRep Module

namespace CompanionTheory.rg.gu.whit

theorem rank_le_one_iff_dual (W : Type) [AddCommGroup W] [Module ℂ W] :
    Module.rank ℂ W ≤ 1 ↔ Module.rank ℂ (Module.Dual ℂ W) ≤ 1 := by
  by_cases hf : Module.Finite ℂ W
  · rw [Module.dual_rank_eq, Cardinal.lift_id]
  · have h0 : Cardinal.aleph0 ≤ Module.rank ℂ W := not_lt.1 (fun h => hf (rank_lt_aleph0_iff.1 h))
    have h1 := rank_lt_rank_dual h0
    constructor
    · intro h
      exact absurd (h0.trans h) (not_le.2 Cardinal.one_lt_aleph0)
    · intro h
      exact absurd ((h0.trans h1.le).trans h) (not_le.2 Cardinal.one_lt_aleph0)

theorem rank_twJacquet_le_one_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) :
    Module.rank ℂ (TwJacquet ρ N θ) ≤ 1 ↔
      Module.rank ℂ (GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ))) ≤ 1 := by
  have hE : GroundTheory.Automorphic.Whittaker.equivariantFunctionals ρ (fun u : N => ((θ u : ℂˣ) : ℂ)) =
      (twKer ρ N θ).dualAnnihilator := by
    ext ℓ
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro h w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, v, rfl⟩ := hx
        rw [map_sub, map_smul, h n v, smul_eq_mul, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    · intro h n v
      have := h _ (Submodule.subset_span ⟨n, v, rfl⟩)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
      exact this
  rw [rank_le_one_iff_dual, hE, ← (Submodule.dualQuotEquivDualAnnihilator _).rank_eq]

end CompanionTheory.rg.gu.whit
