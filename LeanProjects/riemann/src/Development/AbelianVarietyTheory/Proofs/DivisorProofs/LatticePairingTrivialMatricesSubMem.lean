import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShapeBd

variable {D : D7} {a a' : ℕ}

theorem symp_add_left' (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E))
    (x x' y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB (x + x') y =
      GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB x y +
        GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB x' y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add]

theorem det_ne_zero_skew (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) {d : ℕ} (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    {r s : ℕ} (hY : Y.IsSkew D.sp.cm.sig B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hY.sig w)
  intro h0
  apply h
  have hm : (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det := (RingHom.map_det _ _).symm
  rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]

theorem exists_local (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : Fv D.host.F v) :
    ∃ e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) e ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ e = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp D.sp.cm.sig) e = c := by
  refine ⟨GlobalTheory.SrcHalfOne.plcC τ c, ?_, GlobalTheory.SrcHalfOne.piW_plcC τ c, ?_⟩
  · intro u hu
    have h0 : u * GlobalTheory.LatVac.liftV v c = 0 := GlobalTheory.LatVac.at_liftV v c u hu
    change u • (Formalism.L2.Theta.cA D (GlobalTheory.EmbChart.idem τ) *
      algebraMap (AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) (GlobalTheory.LatVac.liftV v c)) = 0
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, h0, map_zero, mul_zero]
  · have h := GlobalTheory.SrcHalfOne.piW_cA_plcC τ c
    rw [GlobalTheory.SrcHalfOne.piW_cA] at h
    exact h

theorem coBar_onto (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (hV' : Γ.V'.J.det ≠ 0) (hW : Γ.W.J.det ≠ 0) (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
        GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := (Γ.W.J.map Bs.τ₁)ᵀ with hBdef
  have hA : IsUnit A.det := by
    rw [isUnit_iff_ne_zero, hAdef]
    have hm : (Γ.V'.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hV'
  have hB : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, hBdef, Matrix.det_transpose]
    have hm : (Γ.W.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hW
  choose e he using fun c => exists_local (D := D) Bs.v₁ Bs.τ₁ c
  set z : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) := -(A⁻¹ * Y * B⁻¹) with hz
  refine ⟨z.map e, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (he (z i j)).1 u hu
  · funext i j
    exact (he (z i j)).2.1
  · have hx : (z.map e).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = z := by
      funext i j
      exact (he (z i j)).2.2
    unfold GlobalTheory.VacShape.coBar
    rw [hx, ← hAdef, ← hBdef, hz]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]

theorem bd_sub : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ Y h hY hYh
  have hV' := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D Bs Γ.V' hTr.geo.hV'
  have hW := det_ne_zero_skew Bs Γ.W hTr.geo.hW
  intro x hx hx0 hxh u hu hu0
  obtain ⟨x', hx', hx'0, hx'Y⟩ := coBar_onto Bs Γ hV' hW Y
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (x' + x) := by
    intro w hw
    rw [smul_add, hx' w hw, hx w hw, add_zero]
  have h1 := hYh (x' + x) hat (by rw [Matrix.map_add _ (map_add _), hx'0, hx0, add_zero])
    (by rw [GlobalTheory.VacShape.coBar_add, hx'Y, hxh]) u hu hu0
  have h2 := hY x' hx' hx'0 hx'Y u hu hu0
  rw [symp_add_left', AddChar.map_add_eq_mul, h2, one_mul] at h1
  exact h1

end GlobalTheory.VacShapeBd

end
