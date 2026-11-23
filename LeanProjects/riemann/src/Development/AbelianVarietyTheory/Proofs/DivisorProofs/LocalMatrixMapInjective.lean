import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

theorem isUnit_det_dbl_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : J.det ≠ 0) :
    IsUnit ((dbl J).map t).det := by
  have e : ((dbl J).map t).det = (t : E →+* Fv F v) (dbl J).det := by
    rw [RingHom.map_det]; rfl
  rw [e, isUnit_iff_ne_zero]
  have hd : (dbl J).det ≠ 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact mul_ne_zero hJ (mul_ne_zero (pow_ne_zero _ (by simp)) hJ)
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hd

theorem unitary_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl F} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (X : UD σ J) :
    ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t))ᵀ * (dbl J).map t *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) = (dbl J).map t := by
  have hX : (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J) := X.2
  have h := congrArg (fun M => M.map (piW t)) hX
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have eD : (dbl (incM F J)).map (piW t) = (dbl J).map t := by
    ext (i | i) (j | j) <;> simp [dbl, incM, GlobalTheory.Div.CoordOpp.piW_inclR]
  have eC : ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ)).map (piW t) =
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) := by
    ext i j; simp [GlobalTheory.Div.CoordOpp.piW_cA]
  rw [eD, eC] at h
  simpa [Matrix.transpose_map] using h

end GlobalTheory.DblScal

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.locMatD_injOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.InjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) := by
  intro F E _ _ _ _ _ σ hcm d J hJ v t c p hp q hq hpq
  set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := p.1.val with hPdef
  set Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := q.1.val with hQdef

  have e0 : (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c =
      (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) q.1 * dsum c := hpq
  have eG := mul_left_cancel (mul_right_cancel e0)
  have h1 : P.map (piW t) = Q.map (piW t) := congrArg Units.val eG

  have h2 : P.map (piW (t.comp σ)) = Q.map (piW (t.comp σ)) := by
    have hUp := unitary_at t p
    have hUq := unitary_at t q
    rw [← hPdef] at hUp
    rw [← hQdef, ← h1] at hUq
    set g := Matrix.GeneralLinearGroup.map (piW t) p.1
    have hg : (g : Matrix _ _ (Fv F v)) = P.map (piW t) := rfl
    have hinv : ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * (P.map (piW t))ᵀ = 1 := by
      rw [← hg, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have e1 : (dbl J).map t * P.map (piW (t.comp σ)) = (dbl J).map t * Q.map (piW (t.comp σ)) := by
      have := hUp.trans hUq.symm
      have := congrArg (fun M => ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * M) this
      simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
    have hD := isUnit_det_dbl_map t hJ
    have := congrArg (fun M => ((dbl J).map t)⁻¹ * M) e1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD, Matrix.one_mul] using this

  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  have hev : evFin F v (1 - e) = 0 := by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hp' : At (evFin F v) (P - 1) := hp
  have hq' : At (evFin F v) (Q - 1) := hq
  have hM : P - Q = e • (P - Q) := by
    have h0 : (1 - e) • (P - Q) = 0 := by
      have : P - Q = (P - 1) - (Q - 1) := by abel
      rw [this, smul_sub, hp' (1 - e) hev, hq' (1 - e) hev, sub_zero]
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine Subtype.ext (Units.ext ?_)
  change P = Q
  rw [← sub_eq_zero, hM]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  apply GlobalTheory.InertVacIso.smul_eq_zero_of_compFin
  apply GlobalTheory.AdelicU.split_ext hcm t
  · change piW t ((P - Q) i j) = splitProj t 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h1 i) j
  · change piW (t.comp σ) ((P - Q) i j) = splitProj (t.comp σ) 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h2 i) j

end
