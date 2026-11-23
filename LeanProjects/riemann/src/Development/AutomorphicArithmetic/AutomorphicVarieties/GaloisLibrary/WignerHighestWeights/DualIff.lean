import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.GlNegOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible.QuantumDeterminantDual

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem qdet_negT {d n : ℕ} (X : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (h : Formalism.REAL.GlRel X) (u : ℂ) :
    Formalism.REAL.qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2) =
      (-1 : ℂ) ^ n • (Formalism.REAL.qdet X (-u + ((n : ℂ) - 1) / 2))ᵀ := by
  have h1 := map_qdet (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2)
  have h2 := (glNegOp _ n X h).2 (u + ((n : ℂ) - 1) / 2)
  have e : (fun i j => (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (-(X i j)ᵀ)) =
      fun i j => -MulOpposite.op (X i j) := by
    funext i j
    simp
  have e' : (n : ℂ) - 1 - (u + ((n : ℂ) - 1) / 2) = -u + ((n : ℂ) - 1) / 2 := by ring
  rw [e, h2, e'] at h1
  have h3 : (Formalism.REAL.qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2))ᵀ =
      (-1 : ℂ) ^ n • Formalism.REAL.qdet X (-u + ((n : ℂ) - 1) / 2) := MulOpposite.op_injective h1
  rw [← Matrix.transpose_smul, ← h3, Matrix.transpose_transpose]

private theorem prod_neg (m : Multiset ℂ) (u : ℂ) :
    ((m.map Neg.neg).map (-u + ·)).prod = (-1) ^ Multiset.card m * (m.map (u + ·)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]
    ring

end UpperTheory.V.AlgRepEndIrreducible.QuantumDeterminantDual

theorem UpperTheory.V.AlgRepEndIrreducible.dualIff :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ),
      UpperTheory.V.Af.AlgInfChar Ξ τ (m.map Neg.neg) ↔ GlobalTheory.WignerGL.HasDualInfChar Ξ τ m := by
  intro E _ _ _ a Ξ τ m
  have hR : Formalism.REAL.GlRel (eL Ξ.dmat τ) := (eLRel E a _ Ξ.dmat (GlobalTheory.AlgInfChar.dmat_bracket Ξ)).1 τ
  have hd : GlobalTheory.WignerGL.dualE Ξ τ = fun i j => -(eL Ξ.dmat τ i j)ᵀ := by
    funext i j
    exact dualE_eq Ξ τ i j
  have hs : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by rw [← mul_pow]; simp
  change (Multiset.card (m.map Neg.neg) = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (eL Ξ.dmat τ) (u + ((a : ℂ) - 1) / 2) =
    ((m.map Neg.neg).map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) ↔ _
  unfold GlobalTheory.WignerGL.HasDualInfChar
  rw [Multiset.card_map, hd]
  refine and_congr_right fun hm => ⟨fun h u => ?_, fun h u => ?_⟩
  · rw [QuantumDeterminantDual.qdet_negT _ hR, h, QuantumDeterminantDual.prod_neg, hm, Matrix.transpose_smul, Matrix.transpose_one, smul_smul,
      ← mul_assoc, hs, one_mul]
  · have h1 := congrArg (fun M => (-1 : ℂ) ^ a • Mᵀ) (h (-u))
    have h2 := QuantumDeterminantDual.prod_neg m (-u)
    simp only [QuantumDeterminantDual.qdet_negT _ hR, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_one,
      smul_smul, hs, one_smul, neg_neg] at h1
    rw [neg_neg, hm] at h2
    rw [h1, h2]
