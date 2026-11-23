import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

open GlobalTheory.OppLagr in

theorem GlobalTheory.OppLagr.act_linBar : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinBar B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omB (chrW χW t) (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  have hcm : IsCMExt F E σ := hP.base.cm
  have hJX : (X.J.map t).det ≠ 0 := det_map_ne_zero (det_ne_zero_herm hP.herm) t
  have hJW : (W.J.map t).det ≠ 0 := det_map_ne_zero (det_ne_zero_skew hP.skew) t
  have hb : b.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hc : c.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp c.isUnit).ne_zero
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(b.1ᵀ * X.J.map t)) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hb hJX)))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (c.1ᵀ * W.J.map t) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hc hJW))
  have hPv : P.1 = -(b.1ᵀ * X.J.map t) := rfl
  have hQv : Q.1 = c.1ᵀ * W.J.map t := rfl
  have hW2 : M.IsLinW B.ψ (t.comp σ) P⁻¹ Q⁻¹ ι := by
    unfold Model.IsLinW
    unfold Model.IsLinBar at hι
    rw [comp_comp hcm]
    convert hι using 2
    funext u
    simp only [inv_inv, hPv, hQv, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_assoc]
  have key := GlobalTheory.T.linear_witt_model_unitary_action hPr F E σ B n d X W M χX χW om r s r' s' hP v (t.comp σ) P⁻¹ Q⁻¹ ι hW2 g hg h hh φ hφ φ₁ hφ₁ hA
  have eg : locMat (t.comp σ) P⁻¹ g = GlobalTheory.SplitFlip.invT (locMat t b g) := by
    change P⁻¹⁻¹ * _ * P⁻¹ = GlobalTheory.SplitFlip.invT (b⁻¹ * _ * b)
    rw [inv_inv]
    exact conj_eq_invT b P _ _ (X.J.map t) (-1) (GlobalTheory.Div.CoordOpp.unit_map σ g t) (by rw [hPv, neg_one_smul])
  have eh : locMat (t.comp σ) Q⁻¹ h = GlobalTheory.SplitFlip.invT (locMat t c h) := by
    change Q⁻¹⁻¹ * _ * Q⁻¹ = GlobalTheory.SplitFlip.invT (c⁻¹ * _ * c)
    rw [inv_inv]
    exact conj_eq_invT c Q _ _ (W.J.map t) 1 (GlobalTheory.Div.CoordOpp.unit_map σ h t) (by rw [hQv, one_smul])
  rw [key, eg, eh, chrW_comp hcm χW hP.resW, chrW_comp hcm χX hP.resX, inv_inv, omA_invT]
