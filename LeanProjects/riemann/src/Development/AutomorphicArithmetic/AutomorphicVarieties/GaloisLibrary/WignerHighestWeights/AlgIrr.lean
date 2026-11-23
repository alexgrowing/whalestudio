import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.PairAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.algIrr :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a), IsMultiGl (eEnd Ξ) ∧ ∀ W, Stab (eEnd Ξ) W → W = ⊥ ∨ W = ⊤ := by
  intro E _ _ _ a Ξ
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨h1, h2⟩ := eLRel E a _ Ξ.dmat (GlobalTheory.AlgInfChar.dmat_bracket Ξ)
    let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
    have hf : ∀ τ i j, eEnd Ξ τ i j = f (eL Ξ.dmat τ i j) := fun _ _ _ => rfl
    refine ⟨fun τ i j k l => ?_, fun s t hst i j k l => ?_⟩
    · have h := congrArg f (h1 τ i j k l)
      simpa only [hf, map_sub, map_mul, apply_ite f, map_zero] using h
    · rw [hf, hf, ← map_mul, ← map_mul, h2 s t hst]
  · let S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) :=
      { carrier := {p | ∀ w ∈ W, p.1 *ᵥ w ∈ W}
        mul_mem' := fun {p q} hp hq w hw => by
          rw [Prod.fst_mul, ← Matrix.mulVec_mulVec]
          exact hp _ (hq w hw)
        add_mem' := fun {p q} hp hq w hw => by
          rw [Prod.fst_add, Matrix.add_mulVec]
          exact W.add_mem (hp w hw) (hq w hw)
        algebraMap_mem' := fun c w hw => by
          rw [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.fst_one, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem c hw }
    exact Ξ.irred W fun y v hv => (pairAlg E a Ξ Ξ S fun τ i j w hw => hW τ i j w hw).2 y v hv
