import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have h1 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  have h2 : ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  intro h0
  apply h2
  rw [← h1, Matrix.det_mul, Matrix.det_mul, h0]
  simp

theorem exists_at_coBar_eq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)),
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧ GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  intro D a a' Bs Γ X om om' hTr Y
  have hcm := hTr.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have hV : Γ.V'.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hTr.geo.hV'.sig w)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hW : Γ.W.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hTr.geo.hW.sig w)
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  have hV1 : IsUnit (Γ.V'.J.map Bs.τ₁).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hV
    apply (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective
    rw [map_zero, ← h0]
    exact RingHom.map_det (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J
  have hW1 : IsUnit ((Γ.W.J.map Bs.τ₁)ᵀ).det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro h0
    apply hW
    apply (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective
    rw [map_zero, ← h0]
    exact RingHom.map_det (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J
  set J' := Γ.V'.J.map Bs.τ₁ with hJ'
  set JWt := (Γ.W.J.map Bs.τ₁)ᵀ with hJWt
  let Mx : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) := -(J'⁻¹ * Y * JWt⁻¹)
  obtain ⟨e₀, he₀⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
  set d : Fv D.host.F Bs.v₁ := Bs.τ₁ (D.sp.cm.sig e₀) - Bs.τ₁ e₀ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 fun e => he₀ ((Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁).injective e)
  let z : Fv D.host.F Bs.v₁ → AE D.host.F D.host.E := fun t =>
    GlobalTheory.LatVac.liftV Bs.v₁ (-t * Bs.τ₁ e₀ / d) ⊗ₜ[D.host.F] (1 : D.host.E) +
      GlobalTheory.LatVac.liftV Bs.v₁ (t / d) ⊗ₜ[D.host.F] e₀
  have hpi : ∀ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁) (x : AF D.host.F) (e : D.host.E),
      piW τ (x ⊗ₜ[D.host.F] e) = evFin D.host.F Bs.v₁ x * τ e := fun τ x e => by
    simp only [piW, compFin, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  have hz0 : ∀ t, piW Bs.τ₁ (z t) = 0 := fun t => by
    simp only [z, map_add, hpi, GlobalTheory.LatVac.evFin_liftV, map_one]
    field_simp
    ring
  have hz1 : ∀ t, piW (Bs.τ₁.comp D.sp.cm.sig) (z t) = t := fun t => by
    simp only [z, map_add, hpi, GlobalTheory.LatVac.evFin_liftV, map_one, AlgHom.comp_apply]
    rw [hd] at hd0 ⊢
    field_simp
    ring
  have hzA : ∀ t, At (evFin D.host.F Bs.v₁) (z t) := fun t u hu => by
    simp only [z, smul_add, TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV _ _ u hu, TensorProduct.zero_tmul, add_zero]
  refine ⟨Mx.map z, fun u hu => ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
    exact hzA _ u hu
  · ext i j
    simp only [Matrix.map_apply, Matrix.zero_apply, hz0]
  · unfold coBar
    have hx : (Mx.map z).map (piW (Bs.τ₁.comp D.sp.cm.sig)) = Mx := by
      ext i j
      simp only [Matrix.map_apply, hz1]
    rw [hx]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Mx]
    rw [← hJWt, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hV1, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW1, Matrix.mul_one]

end GlobalTheory.VacShape
