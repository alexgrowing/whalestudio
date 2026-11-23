import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CapKilled

theorem zalg_mem_space : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ)
    (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W →
    ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (z : Module.End ℂ (Sm E b)), z ∈ Zalg E b →
    ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q := by
  intro E _ _ _ b L W hW q z hz ψ hψ
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_space.1 hψ
  refine mem_space.2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Zalg_stable (V := leftInv E b) (fun X _ h => lie_mem_leftInv X h) hz ψ h1
  · exact Zalg_stable (V := fixL E b L) (fun X _ h => lie_mem_fixL L X h) hz ψ h2
  · intro g
    obtain ⟨s, c, hc⟩ := GlobalTheory.HCFct.exists_interp W hW
    have hk : ∀ k : Kinf E b, cptRep E b k ψ = ∑ i : s, (c i).1 k • cptRep E b i.1 ψ := by
      intro k
      apply Subtype.ext
      funext h
      have := hc _ (h3 h) k
      rw [this]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    have e : (fun k : Kinf E b => (cptRep E b k (z ψ)).1 g) =
        ∑ i : s, (z (cptRep E b i.1 ψ)).1 g • (c i).1 := by
      funext k
      have hcomm := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E b k z hz) ψ
      simp only [Module.End.mul_apply] at hcomm
      rw [← hcomm, hk k, map_sum]
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W.sum_mem fun i _ => W.smul_mem _ (c i).2
  · intro τ u
    have hcap : cap (a := b) τ u ∈ Zalg E b := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hp : Polynomial.aeval (cap (a := b) τ u) (q τ u) ∈ Zalg E b := Algebra.adjoin_le (Set.singleton_subset_iff.2 hcap) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    have hcomm := (KilledFin.Zalg_commute hz hp).eq
    have := LinearMap.congr_fun hcomm ψ
    simp only [Module.End.mul_apply] at this
    rw [← this, h4 τ u, map_zero]
  · exact Zalg_stable (V := tame E b) (fun X _ h => lie_mem_tame X h) hz ψ h5

end GlobalTheory.CapKilled
