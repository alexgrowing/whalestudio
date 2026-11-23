import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

section Chg

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frVec_of_frChg {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Type} [CommRing S]
    [Algebra c.F S] {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S} (hC : GlobalTheory.Frames.FrChg g a P P')
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    frVec Y P' hx' σ i = ∑ j, g σ i j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := hC.1
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1
      (hC.2.1 σ i)
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end Chg

end GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory

theorem frVec_isVert_isCombAtG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), GlobalTheory.Frames.FrChg G 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (x : Sp (DualNumber K) ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (M : GlobalTheory.Reg.MChart TF.Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U), IsVert P N' w → ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (GlobalTheory.FlagTan.unip K N' σ * (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF U n e v _hv K _ _ P₀ P hU G hG hB N' w x hx hUx M hM hV σ i
  obtain ⟨y₀, hy₀, hS⟩ := hV
  obtain ⟨P₀', h0⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.cst c K) P₀
  have hC := (GlobalTheory.FlagTan.frMap_iff_frChg hG h0).1 hy₀
  have ew : frX w = frX y₀ := FlagMod.eq_frX y₀ ((FlagMod.frX_fst w).trans hS.1) (FlagMod.frX_snd w)
  have ey : frX y₀ = frX P₀' := FlagMod.eq_frX P₀' ((FlagMod.frX_fst y₀).trans hC.1) (FlagMod.frX_snd y₀)
  have hx₀ : frX y₀ ≫ TF.Y.j = x := ew ▸ hx
  have hx' : frX P₀' ≫ TF.Y.j = x := ey ▸ hx₀
  have e1 := frVec_of_frChg hM hx₀ hx hS σ i
  have e2 := fun j => frVec_of_frChg hM hx' hx₀ hC σ j
  have ecst : spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P₀ ≫ TF.Y.j) = x := by
    rw [← Category.assoc, FlagMod.frX_frMap h0, hx']
  have eev : ev x U.1 hUx = (GlobalTheory.FlagTan.cst c K).toRingHom.comp (ev (frX P₀ ≫ TF.Y.j) U.1 hU) := by
    rw [FlagMod.ev_congr ecst.symm U.1 hUx (ecst ▸ hUx), FlagMod.ev_spMap]
  have e3 : ∀ k, (tv (frVec TF.Y P₀' hx' σ k)).left = spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, k⟩) := by
    intro k
    rw [← FlagMod.tanPull_frVec h0 rfl hx' ecst, FlagMod.tanPull_left, hB σ k, ← Category.assoc, spMap_comp',
      ← dualMap_comp, eev]
  open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections in
  have key : frVec TF.Y w hx σ i = ∑ k, (GlobalTheory.FlagTan.unip K N' σ *
      (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i k • frVec TF.Y P₀' hx' σ k := by
    rw [e1]
    simp_rw [e2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    rfl
  have hv' : (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) =
      fun j => (tv (frVec TF.Y P₀' hx' σ j)).left := funext fun j => (e3 j).symm
  rw [hv', GlobalTheory.LieMet.isComb_iff]
  exact key

end GlobalTheory.LogPole
