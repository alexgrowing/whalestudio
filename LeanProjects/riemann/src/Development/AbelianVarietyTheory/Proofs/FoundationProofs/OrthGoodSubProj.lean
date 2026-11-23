import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem gaMat_mem_coord (hZ : ∀ g, Z.map (B.r g) ≤ Z) (a : MonoidAlgebra K G) {z : Fin B.S.dim → K} (hz : z ∈ B.coord Z) :
    (B.S.gaMat B.r a).mulVec z ∈ B.coord Z := by
  obtain ⟨f, hf, rfl⟩ := hz
  unfold CSD.gaMat
  rw [Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ ⟨B.r t f, hZ t ⟨f, hf, rfl⟩, CyclotomicLifting.equivFun_end (B := B) (B.r t) f⟩

theorem orth_good_sub_proj (h : BlockHyp B ℓ v0 s) (hZ : ∀ g, Z.map (B.r g) ≤ Z)
    (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) {z : Fin B.S.dim → K} (hz : z ∈ B.coord Z) :
    hform B.S.H z ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec ((B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec x) -
      (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec x)) = 0 := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := BlockDat.lf_v_proj h
  obtain ⟨⟨hl1, -⟩, hl3⟩ := BlockDat.lf_lvl_proj h
  have hz2 := (BlockDat.lf_z_proj (Z := Z) h).2
  have hO := orthogonal_tower_projection B.S.H (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) _ (BlockDat.lf_card_inv_ne (ℓ := ℓ)) hv2 hz2
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  have hadj : (B.vE ℓ * B.vPr ℓ)ᴴ * B.S.H = B.S.H * (B.vE ℓ * B.vPr ℓ) := by
    have := group_action_matrix_adjoint K B.S G B.r h.ok.act (goodAt ℓ.X ℓ.P ℓ.ψ)
    rwa [hg.selfAdj, ← hv3] at this
  have h2 : B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.vE ℓ * B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ := by
    rw [h1, hv3, goodAt, (group_action_matrix_hom K B.S G B.r).2, ← hl3, Matrix.mul_assoc, Matrix.mul_assoc, hl1, Matrix.mul_one]
  have h3 : (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec ((B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec x) -
      (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec x) =
      (B.vE ℓ * B.vPr ℓ).mulVec ((1 - B.vE ℓ * B.zE ℓ Z * B.Pq ℓ Z * B.vPr ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec x)) := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.sub_mulVec, h2]
    congr 1
    unfold BlockDat.fE BlockDat.lPr
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.vPr ℓ) (B.vE ℓ), hv1, Matrix.one_mul]
  have h4 : (B.vPr ℓ).mulVec z ∈ B.Z0 ℓ Z := by
    show (B.vE ℓ).mulVec ((B.vPr ℓ).mulVec z) ∈ B.coord Z
    rw [Matrix.mulVec_mulVec, hv3]
    exact gaMat_mem_coord hZ _ hz
  obtain ⟨u, hu⟩ := (subspace_image_spec K _ (B.Z0 ℓ Z)).2.ge h4
  have hu' : (B.vE ℓ * B.vPr ℓ).mulVec z = (B.vE ℓ * B.zE ℓ Z).mulVec u := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu]; rfl
  rw [h3, ← CyclotomicLifting.hform_adj hadj, hu', RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hO, Matrix.zero_mulVec, dotProduct_zero]

end Block

end GlobalTheory.OnCoord
