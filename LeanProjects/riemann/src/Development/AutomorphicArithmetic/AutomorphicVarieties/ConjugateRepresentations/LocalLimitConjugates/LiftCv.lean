import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.RopComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.liftCv :
    UpperTheory.V.Cj.H.LiftCv := by
  intro E _ _ _ a ha μ _ _ T hT T' hL ψ φ F hψ hφ
  obtain ⟨c1, c2, -, c4⟩ := clFacts E a μ
  have hφg : φ ∈ gard μ := Submodule.subset_span ⟨ψ, F, hψ, hφ⟩
  obtain ⟨g1, g2⟩ := hL φ hφg
  let φ' : Sm E a := ⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩
  have hφ'g : φ' ∈ gard μ := Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
    (hc.comp continuous_inv).integrable_of_hasCompactSupport
      (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
  have e : cl μ (T' φ) = cl μ φ' := by
    rw [g2, c4 ψ φ F hψ hφ, c4 ψ φ' (T F) hψ rfl]
    exact ropComm _ _ μ T hT _ hint F
  have hd : (1 : ℂ) • T' φ + (-1 : ℂ) • φ' ∈ gard μ :=
    add_mem (Submodule.smul_mem _ _ g1) (Submodule.smul_mem _ _ hφ'g)
  obtain ⟨d1, d2, -⟩ := gardFacts E a ha μ _ hd
  have h0 := c2 _ d1 d2 (by
    rw [(c1 _ _ 1 (-1) (gardFacts E a ha μ _ g1).2.1 (gardFacts E a ha μ _ hφ'g).2.1).2, e]
    simp)
  have h1 : T' φ = φ' := by
    rw [one_smul, neg_one_smul, add_neg_eq_zero] at h0
    exact h0
  rw [h1]
