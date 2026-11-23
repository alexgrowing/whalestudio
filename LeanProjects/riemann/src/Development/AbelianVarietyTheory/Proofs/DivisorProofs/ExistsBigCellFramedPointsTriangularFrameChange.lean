import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
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

namespace GlobalTheory.LogPole.CellFrames

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Tri

variable {K : Type} [Field K] {m : ℕ}

theorem lowerTri_inv (A : Matrix (Fin m) (Fin m) K) (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, A i i ≠ 0) :
    (∀ i j, i < j → A⁻¹ i j = 0) ∧ ∀ i, A⁻¹ i i * A i i = 1 := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h), fun i => ?_⟩
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul A hdet) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at e
  · exact e
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA j i h, mul_zero]
    · rw [hB' (OrderDual.toDual_lt_toDual.2 h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem frVec_of_comb {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) (e : P'.x = P.x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (cf : Fin (Dw.mult σ) → S) (h3 : IsCombAt P.x (P.u σ) cf (P'.u σ i)) :
    frVec Y P' hx' σ i = ∑ j, cf j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1 h3
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end GlobalTheory.LogPole.CellFrames

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cellFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC K _ _ z hz hk Q hQ
  obtain ⟨-, hWU, -, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun p hp => hWU (hz hp)
  have hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := Category.assoc _ _ _
  have hQx : frX Q ≫ TF.Y.j = z ≫ toBase TF Z := hQ.over.trans hx
  have hvT : ∀ m, IsTanAtG TF.Y.t (z ≫ toBase TF Z) (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hU) (hv.1 m)
  set Lz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (L σ).map (ev z W hz) with hLzd
  set Nz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (N σ).map (ev z W hz) with hNzd
  have hLd : ∀ σ i, Lz σ i i ≠ 0 := fun σ i => ((hLu σ i).map (ev z W hz)).ne_zero
  have hLt : ∀ σ i j, i < j → Lz σ i j = 0 := fun σ i j h => by
    show ev z W hz (L σ i j) = 0
    rw [hLz σ i j h, map_zero]
  have hLinv := fun σ => CellFrames.lowerTri_inv (Lz σ) (hLt σ) (hLd σ)
  have hNdet : ∀ σ, IsUnit (Nz σ).det := fun σ => by
    rw [Matrix.det_of_upperTriangular (M := Nz σ) (fun i j h => by
      show ev z W hz (N σ i j) = 0
      rw [hNz σ i j h, map_zero])]
    refine IsUnit.prod_univ_iff.2 fun i => ?_
    show IsUnit (ev z W hz (N σ i i))
    rw [hN1, map_one]; exact isUnit_one
  have hLdet : ∀ σ, IsUnit (Lz σ).det := fun σ => by
    rw [Matrix.det_of_lowerTriangular (Lz σ) (fun i j h => hLt σ i j (OrderDual.toDual_lt_toDual.1 h))]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hLd σ i)
  have hAdet : ∀ σ, IsUnit (Lz σ * Nz σ).det := fun σ => by
    rw [Matrix.det_mul]; exact (hLdet σ).mul (hNdet σ)
  have hA : ∀ σ, Lz σ * Nz σ = (L σ * N σ).map (ev z W hz) := fun σ => Matrix.map_mul.symm
  have hvec : ∀ σ i, frVec TF.Y Q hQx σ i =
      ∑ j, (Lz σ * Nz σ) i j • GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩)) := fun σ i => by
    rw [hQ.frVec_eq hx hQx σ]
    have h1 := hcomb K z hz hU hk hx σ i
    have h2 := (GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))) _ _).1 h1
    rw [h2, hA]
    rfl
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K Q (fun σ => (Lz σ * Nz σ)⁻¹) 1
    (fun σ => (Matrix.isUnit_nonsing_inv_det_iff).2 (hAdet σ))
  obtain ⟨P, hP, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K P₀ Nz 1 hNdet
  rw [Units.val_one] at hP₀ hP
  have hQP := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).1 _ _ _ _ _ _ _ hP₀).1 hP
  have hg : (fun σ => Nz σ * (Lz σ * Nz σ)⁻¹) = fun σ => (Lz σ)⁻¹ := funext fun σ => by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hNdet σ), Matrix.one_mul]
  rw [hg, _root_.mul_one] at hQP
  let t : Ix Dw → Kˣ := fun ix => Option.elim ix 1 fun p => Units.mk0 ((Lz p.1 p.2 p.2)⁻¹) (inv_ne_zero (hLd _ _))
  have hP₀x : frX P₀ ≫ TF.Y.j = z ≫ toBase TF Z := by
    rw [eq_frX Q ((frX_fst P₀).trans hP₀.1) (frX_snd P₀)]; exact hQx
  have hU' : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1 := hP₀x ▸ hU
  refine ⟨P₀, P, t, hU', ?_, fun σ i => ?_, hP, fun σ i => ?_⟩
  · refine (GlobalTheory.Frames.frBor_iff_frChg Q P t).2 ⟨fun σ => (Lz σ)⁻¹, fun σ i j h => (hLinv σ).1 i j h,
      fun σ i => eq_inv_of_mul_eq_one_left ((hLinv σ).2 i), ?_⟩
    show GlobalTheory.Frames.FrChg _ ((1 : Kˣ) : K) Q P
    rw [Units.val_one]
    exact hQP
  · show (Lz σ i i)⁻¹ * Lz σ i i = 1
    exact inv_mul_cancel₀ (hLd σ i)
  · have h0 := CellFrames.frVec_of_comb (TF.X.F.inM hk hx) hQx hP₀x hP₀.1 σ i _ (hP₀.2.1 σ i)
    have hI := Matrix.nonsing_inv_mul _ (hAdet σ)
    have key : frVec TF.Y P₀ hP₀x σ i = GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, i⟩)) := by
      rw [h0]
      simp only [hvec, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      have e2 : ∀ l, (∑ j, (Lz σ * Nz σ)⁻¹ i j * (Lz σ * Nz σ) j l) = (1 : Matrix _ _ K) i l := fun l => by
        rw [← hI, Matrix.mul_apply]
      simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : (tv (frVec TF.Y P₀ rfl σ i)).left = (tv (frVec TF.Y P₀ hP₀x σ i)).left := rfl
    rw [e1, key, GlobalTheory.LieMet.left_tanOf, ev_congr hP₀x U.1 hU' hU]

end GlobalTheory.LogPole
