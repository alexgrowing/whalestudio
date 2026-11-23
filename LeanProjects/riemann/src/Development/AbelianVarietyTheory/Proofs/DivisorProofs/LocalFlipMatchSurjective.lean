import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone GlobalTheory.EvZeroStd
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitCoords

theorem exists_at_two_comps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) {n d : ℕ}
    (A A' : Matrix (Fin n) (Fin d) (Fv F v)) :
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u ∧ u.map (piW t) = A ∧ u.map (piW (t.comp σ)) = A' := by
  refine ⟨Matrix.of fun i j => GlobalTheory.EmbChart.tensAt E v ((GlobalTheory.AdelicU.splitAlgEquiv h t).symm (A i j, A' i j)), ?_, ?_, ?_⟩
  · intro a ha
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Algebra.smul_def, mul_comm, GlobalTheory.EmbChart.tensAt_mul_right, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    have : GlobalTheory.AdelicU.compFin F E v (a ⊗ₜ[F] (1 : E)) = 0 := by
      change evFin F v a ⊗ₜ[F] (1 : E) = 0
      rw [ha, TensorProduct.zero_tmul]
    rw [this, mul_zero, LinearMap.map_zero]
  · refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.of_apply]
    change GlobalTheory.AdelicU.splitProj t (GlobalTheory.AdelicU.compFin F E v (GlobalTheory.EmbChart.tensAt E v _)) = _
    rw [GlobalTheory.EmbChart.compFin_tensAt, GlobalTheory.AdelicU.splitProj_symm]
  · refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.of_apply]
    change GlobalTheory.AdelicU.splitProj (t.comp σ) (GlobalTheory.AdelicU.compFin F E v (GlobalTheory.EmbChart.tensAt E v _)) = _
    rw [GlobalTheory.EmbChart.compFin_tensAt, GlobalTheory.AdelicU.splitProj_comp_symm]

end GlobalTheory.SplitCoords

open GlobalTheory.SplitCoords in
theorem GlobalTheory.SplitCoords.coords_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 →
    ∀ {v : Pl F} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (P Q : Matrix (Fin n) (Fin d) (Fv F v)),
      ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u ∧ GlobalTheory.FlipMatch.coX t b c u = P ∧
        GlobalTheory.FlipMatch.coY σ X Y t b c u = Q := by
  intro F E _ _ _ _ _ σ h n d X Y hX hY v t b c P Q
  have hdX : IsUnit (X.J.map t).det := by
    have e : (X.J.map t).det = t X.J.det := (RingHom.map_det (t : E →+* Fv F v) X.J).symm
    rw [e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hX))
  have hdY : IsUnit ((Y.J.map t)ᵀ).det := by
    have e : (Y.J.map t).det = t Y.J.det := (RingHom.map_det (t : E →+* Fv F v) Y.J).symm
    rw [Matrix.det_transpose, e]; exact (isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hY))
  obtain ⟨u, hu, h1, h2⟩ := exists_at_two_comps h t (b.1 * P * c.1ᵀ)
    (-((X.J.map t)⁻¹ * (b⁻¹).1ᵀ * Q * (c⁻¹).1 * ((Y.J.map t)ᵀ)⁻¹))
  refine ⟨u, hu, ?_, ?_⟩
  · unfold GlobalTheory.FlipMatch.coX
    rw [h1]
    have hb : (b⁻¹).1 * b.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; rfl
    have hc : c.1ᵀ * (c⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; exact Matrix.transpose_one
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.one_mul, Matrix.mul_assoc, hc, Matrix.mul_one]
  · unfold GlobalTheory.FlipMatch.coY
    rw [h2]
    have hb : b.1ᵀ * (b⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; exact Matrix.transpose_one
    have hc : (c⁻¹).1 * c.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel]; rfl
    have e1 : X.J.map t * (X.J.map t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdX
    have e2 : ((Y.J.map t)ᵀ)⁻¹ * (Y.J.map t)ᵀ = 1 := Matrix.nonsing_inv_mul _ hdY
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (X.J.map t), e1, Matrix.one_mul, ← Matrix.mul_assoc b.1ᵀ, hb, Matrix.one_mul,
      ← Matrix.mul_assoc (((Y.J.map t)ᵀ)⁻¹), e2, Matrix.one_mul, hc, Matrix.mul_one]
