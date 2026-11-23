import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.oneEig :
    UpperTheory.V.Lit.Bor.OneEig := by
  intro E _ _ _ a π Ξ r hr hC
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π 1
  have hc' : ∀ ψ ∈ π.V, lie E a (oneL E a) ψ = c • ψ := hc
  have h0 : c + (r : ℂ) = 0 := by
    by_contra hne
    refine not_hasCohomology_of_central hne (fun m => ?_) hC
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul φ v =>
      have e : π.op (.lie (oneL E a)) φ = c • φ := Subtype.ext (hc' φ.1 φ.2)
      have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
      rw [tensorLie_tmul, e, hr', Matrix.smul_mulVec, Matrix.one_mulVec, add_smul, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul]
  intro φ hφ
  rw [hc' φ hφ, eq_neg_of_add_eq_zero_left h0]
