import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BigTop.Fun

open Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix

theorem iC_cpt_eq_theta_toR {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding z) = X.Θ t (X.jR t (cr.toR X.zs b t z)) := by
  conv_rhs => rw [pi_eq_sum_univ z]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, iC, lin, Fintype.linearCombination_apply, cpt]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 4
  ext j
  simp [Pi.single_apply, eq_comm]

theorem theta_jR_eq_zero_of_perp {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hJ : X.JIsoR cv) (hZ : X.RatZ) (t : Bs.Tup) (x : A.FR t) (hx : ∀ w ∈ X.Z t, cv.hR t w x = 0) :
    X.Θ t (X.jR t x) = 0 := by
  have hperp : ∀ m ∈ Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))), ⟪m, X.jR t x⟫_ℂ = 0 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨w, hw, rfl⟩ := hm
      rw [hJ t w x, hx w hw, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  refine ext_inner_left ℂ fun e => ?_
  rw [inner_zero_right, ← LinearMap.adjoint_inner_left]
  apply hperp
  rw [hZ.1 t]
  exact LinearMap.mem_range_self _ _

theorem sub_zE_Pq_mem_U {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (hs : Function.Surjective (B.Pq ℓ Z).mulVec)
    (y : Fin (B.nV ℓ) → K) : y - (B.zE ℓ Z).mulVec ((B.Pq ℓ Z).mulVec y) ∈ B.U ℓ Z := by
  set E := B.zE ℓ Z with hE
  set H := B.HV ℓ with hH
  have hdet : IsUnit (Eᴴ * H * E).det := by
    by_contra hu
    have h0 : B.Pq ℓ Z = 0 := by
      show (Eᴴ * H * E)⁻¹ * (Eᴴ * H) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.zero_mul]
    apply hu
    have hd : B.dZ ℓ Z = 0 := by
      by_contra hne
      obtain ⟨i⟩ : Nonempty (Fin (B.dZ ℓ Z)) := ⟨⟨0, Nat.pos_of_ne_zero hne⟩⟩
      obtain ⟨x, hx⟩ := hs (Pi.single i 1)
      rw [h0, Matrix.zero_mulVec] at hx
      have := congrFun hx i
      simp at this
    have : IsEmpty (Fin (B.dZ ℓ Z)) := ⟨fun i => by have := i.2; omega⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  have hO := (Formalism.DivisionValues.exponent_index_lattice.isOrthProj_formula H E hdet).2
  intro z hz
  obtain ⟨c, rfl⟩ : ∃ c, E.mulVec c = z := by
    have h := (Formalism.L2.DIV.subspace_image_spec K _ (B.Z0 ℓ Z)).2
    have : z ∈ LinearMap.range (subE (B.Z0 ℓ Z)).mulVecLin := by rw [h]; exact hz
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have : Eᴴ *ᵥ (H *ᵥ (y - E *ᵥ (B.Pq ℓ Z *ᵥ y))) = (Eᴴ * H * (1 - E * B.Pq ℓ Z)) *ᵥ y := by
    simp only [Matrix.mulVec_sub, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_one, Matrix.mul_assoc]
  rw [this]
  show star c ⬝ᵥ (Eᴴ * H * (1 - E * ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)))) *ᵥ y = 0
  rw [hO, Matrix.zero_mulVec, dotProduct_zero]

theorem csum_goodPart_perp_eq_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (s : ℕ) (hB : B.Ok s) (v0 : InfinitePlace K) (hv : Formalism.DivisionValues.IsConjAt v0) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (u : Fin (B.nV ℓ) → K) (hu : u ∈ B.U ℓ Z) (w : B.S.Forms) (hw : w ∈ Z) :
    B.S.csum (w : B.S.Cl → B.S.V) ((B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = 0 := by
  classical
  have hpe := good_at_spec K v0 hv G ℓ.X hX ℓ.P ℓ.ψ
  obtain ⟨hO, hEP⟩ := orthogonal_projection_spec K v0 hv B.S (hB.hpos v0) G B.r hB.act _ hpe.idem hpe.selfAdj
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt ℓ.X ℓ.P ℓ.ψ)
  rw [hpe.selfAdj] at hadj
  have hE : B.vE ℓ = B.S.cutE B.r (goodAt ℓ.X ℓ.P ℓ.ψ) := rfl
  set Gm := B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) with hGm
  set E := B.vE ℓ with hEdef
  set x := B.S.basis.equivFun w with hx
  have hw' : (w : B.S.Cl → B.S.V) = B.S.I x := by simp [CSD.I, x]
  have hv' : ((B.S.basis.equivFun.symm (E.mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I (E.mulVec u) := rfl
  rw [hw', hv', CSD.csum_sum, ← Formalism.DivisionValues.RationalHermitianForm.hform_apply]
  have hGE : Gm *ᵥ (E *ᵥ u) = E *ᵥ u := by
    have hO1 : B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) * E = 1 := hO.1
    rw [← hEP, Matrix.mulVec_mulVec, ← hE, Matrix.mul_assoc, hO1, Matrix.mul_one]
  rw [← hGE]
  have hmove : Formalism.DivisionValues.hform B.S.H x (Gm *ᵥ (E *ᵥ u)) = Formalism.DivisionValues.hform B.S.H (Gm *ᵥ x) (E *ᵥ u) := by
    rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.mulVec_mulVec, ← hadj,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  set z' := B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ x with hz'def
  have hGx : Gm *ᵥ x = E *ᵥ z' := by rw [← hEP, ← Matrix.mulVec_mulVec, hE]
  have hz' : z' ∈ B.Z0 ℓ Z := by
    show (E.mulVecLin z') ∈ B.coord Z
    rw [Matrix.mulVecLin_apply, ← hGx]
    refine ⟨B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w, ?_, ?_⟩
    · show (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w) ∈ Z
      simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t hw)
    · simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hGm,
        CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec]
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      show B.S.basis.equivFun (B.r t w) = (LinearMap.toMatrix B.S.basis B.S.basis (B.r t)) *ᵥ (B.S.basis.equivFun w)
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rw [hmove, hGx, ← Formalism.L2.DIV.hform_cut]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : Eᴴ * B.S.H * E = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [hEdef, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hP, one_smul]
  rw [hH, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.smul_mulVec, dotProduct_smul, ← Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot,
    hu z' hz', smul_zero]

set_option maxHeartbeats 1000000 in

theorem theta_eV0_eq_iC_Pq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp t y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  rw [iC_cpt_eq_theta_toR, TieModel.toR_eq]
  let y' : Fin ((p.P.A3.A.fam.R t).nV (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)) → D.what₂.LL := y
  have hu := sub_zE_Pq_mem_U (p.P.A3.A.fam.R t) (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)
    ((hCx.wf false).Pq_surj t) y'
  have h := theta_jR_eq_zero_of_perp _ p.F.cv hCx.jIsoR hCx.ratZ t (eV0 p t (y' - ((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y))) (fun w hw =>
    csum_goodPart_perp_eq_zero (p.P.A3.A.fam.R t) 1 (hp.ok.ok2.what₂ t) _ hp.ok.ok2.conj _ hp.ok.ok2.irr _
      (fun g => Submodule.map_le_iff_le_comap.mp (hCx.stable.1 t (Sum.inr g))) _ hu w hw)
  erw [(eV0 p t).map_sub] at h
  have h2 := ((p.R.toCx3 p.F).jR t).map_sub (eV0 p t y') (eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y)))
  erw [h2, map_sub] at h
  exact sub_eq_zero.mp h

end GlobalTheory.BigTop.Fun

end
