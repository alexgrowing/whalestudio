import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedPairLineIff
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.ContraPair in
private theorem paired_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π π' : CuspSub E n}
    (h : Paired π π' conjOp) (α ξ : HChar E)
    (hf : ∀ k : GL (Fin n) (Af E), opMul α (.fin k) * opMul ξ (conjOp (.fin k)) = 1)
    (hk : ∀ k : Kinf E n, opMul α (.cpt k) * opMul ξ (conjOp (.cpt k)) = 1)
    (hl : ∀ X : Lie E n, opAdd α (.lie X) + opAdd ξ (conjOp (.lie X)) = 0) :
    Paired (π.twist α) (π'.twist ξ) conjOp := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  let T := π.toTwist α
  let S := π'.toTwist ξ
  refine ⟨B.compl₁₂ T.symm.toLinearMap S.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (S ψ))
  · exact S.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))
  all_goals
    obtain ⟨φ, rfl⟩ := T.surjective φ
    obtain ⟨ψ, rfl⟩ := S.surjective ψ
    simp only [T, S, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · have e := h3 k φ ψ
    have e' := congrArg Units.val (hf k)
    simp only [conjOp, Units.val_mul, Units.val_one] at e e' ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    linear_combination (B φ ψ) * e'
  · have e := h4 k φ ψ
    have e' := congrArg Units.val (hk k)
    simp only [conjOp, Units.val_mul, Units.val_one] at e e' ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    linear_combination (B φ ψ) * e'
  · have e := h5 X φ ψ
    have e' := hl X
    have e3 : opMul ξ (conjOp (.lie X)) = 1 := rfl
    have e4 : opMul α (.lie X) = 1 := rfl
    rw [e3, e4]
    simp only [Units.val_one, one_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination e + (B φ ψ) * e'

private theorem chiDet_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : HChar E) (g : GA E n) :
    chiDet n (GlobalTheory.ThetaPull.thetaChar χ) g = chiDet n χ (GlobalTheory.ThetaPull.thetaA E n g) :=
  ((congrArg χ.1 (det_thetaGL _ g)).trans (map_inv χ.1 _)).symm

theorem UpperTheory.V.Af.Cq.csdTwist :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (ψ ξ : HChar E), GlobalTheory.ContraPair.DualIsConjBy P ψ →
        compNorm E (GlobalTheory.HeightCounting.Blocks.resReal ξ) = ψ⁻¹ → GlobalTheory.ContraPair.DualIsConj (P.twist ξ) := by
  intro E _ _ _ n P ψ ξ h e
  have e1 := GlobalTheory.HeightCounting.Blocks.mul_inv_compNorm ξ
  have e2 : ψ⁻¹ * GlobalTheory.ThetaPull.thetaChar ξ = ξ := by
    rw [← e1, e, mul_comm ξ, mul_inv_cancel_left]
  have h' := paired_twist h (GlobalTheory.ThetaPull.thetaChar ξ) ξ (fun k => ?_) (fun k => ?_) (fun X => ?_)
  · rwa [← CuspSub.twist_mul, e2] at h'
  · have a := GlobalTheory.ContraPair.Model.sc_fin ξ k
    apply Units.ext
    simp only [thetaOp, GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_one, add_zero] at a
    simp only [opMul, chiDet_theta, GlobalTheory.ThetaPull.thetaA_finGL, Units.val_mul, Units.val_one]
    exact a
  · have a := GlobalTheory.ContraPair.Model.sc_cpt ξ k
    apply Units.ext
    simp only [thetaOp, GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_one, add_zero] at a
    simp only [opMul, chiDet_theta, GlobalTheory.ThetaPull.thetaA_infGL, Units.val_mul, Units.val_one,
      ← toUnits_conj_PhiK]
    exact a
  · have a := GlobalTheory.ContraPair.Model.dualIsConjBy_resReal ξ
    rw [GlobalTheory.ContraPair.DualIsConjBy, ← CuspSub.twist_mul, e1] at a
    have b := ((GlobalTheory.ContraPair.Model.paired_line_iff _ _ _ _).1 a).2.2 (fun _ _ => (Matrix.of X).trace)
    simp only [GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_zero, zero_add] at b ⊢
    simpa [Matrix.trace, star_sum] using b
