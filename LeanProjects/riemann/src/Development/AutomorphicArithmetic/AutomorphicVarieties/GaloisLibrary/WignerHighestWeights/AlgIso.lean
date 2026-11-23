import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIsoLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.PairAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def pairSub {d d' : ℕ} (T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d' → ℂ)) :
    Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ) where
  carrier := {p | ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v}
  mul_mem' := by
    intro p q hp hq v
    have hp' : ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v := hp
    have hq' : ∀ v, T (q.1 *ᵥ v) = q.2 *ᵥ T v := hq
    rw [Prod.fst_mul, Prod.snd_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp', hq']
  add_mem' := by
    intro p q hp hq v
    have hp' : ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v := hp
    have hq' : ∀ v, T (q.1 *ᵥ v) = q.2 *ᵥ T v := hq
    rw [Prod.fst_add, Prod.snd_add, Matrix.add_mulVec, Matrix.add_mulVec, map_add, hp', hq']
  algebraMap_mem' := by
    intro c v
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

theorem UpperTheory.V.AlgRepEndIrreducible.algIso :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ),
      (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ τ (m τ)) → (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ' τ (m τ)) → ∃ T, IsAlgIso Ξ Ξ' T := by
  intro E _ _ _ a Ξ Ξ' m h h'
  obtain ⟨T, hT⟩ := algIsoLie E a Ξ Ξ' m h h'
  obtain ⟨h1, h2⟩ := pairAlg E a Ξ Ξ' (pairSub T) (fun τ i j v => hT τ i j v)
  exact ⟨T, fun y v => h2 y v, fun X v => h1 X v⟩
