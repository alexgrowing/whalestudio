import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.CapDegUniformiserLine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)

namespace GlobalTheory.ShFam.Pad.IthCheck

open NModel

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}

theorem vDeg_symm (d : ℕ) (D D' : Z.VDivZ) (Q : PicSym Z.X) :
    Z.vDeg d D (firstChernPic (Z.vCls D') * Q) = Z.vDeg d D' (firstChernPic (Z.vCls D) * Q) := by
  rw [vDeg_apply, vDeg_apply]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [map_mul (picSymPull _), map_mul (picSymPull _), picSymPull_c1Pic, picSymPull_c1Pic, ← vCls_vRes, ← vCls_vRes]
  exact Check.vDeg_symm _ _ _

theorem capDeg_vp_symm (p d : ℕ) (D D' : Z.VDivQ) (Q : PicSym Z.X) :
    Z.capDeg_vp p d D (Z.cDQ D' * Q) = Z.capDeg_vp p d D' (Z.cDQ D * Q) := by
  induction D using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_mul, LinearMap.add_apply, ha, hb]
  | tmul a D =>
    induction D' using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_mul, LinearMap.add_apply, ha, hb]
    | tmul b D' =>
      have h (a : ℚ) (D : Z.VDivZ) : (a ⊗ₜ[ℤ] D : Z.VDivQ) = a • toQ D := by
        simp [toQ, TensorProduct.smul_tmul']
      simp only [h, map_smul, smul_mul_assoc, LinearMap.smul_apply, cDQ_toQ, capDeg_vp_toQ,
        vDeg_symm d D D', smul_eq_mul]
      ring

def compLB (Z : NModel O) : LB Z.X := ⟨Z.Comp, fun C => C.opens, fun _ _ => 1⟩

theorem isLB_compLB : (compLB Z).IsLB :=
  ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 (Z.exists_comp x), fun _ => map_one _, fun _ _ _ => by
    change res _ 1 * res _ 1 = res _ 1
    rw [map_one, map_one, map_one, mul_one]⟩

def compPair (g : Z.Comp → O) (hg : ∀ C, g C ≠ 0) : VPair Z :=
  .ofUnits (compLB Z) isLB_compLB (fun C => resG Z.X le_top (Z.const (g C)))
    (fun C => Z.isUnit_const (hg C) inf_le_left) fun C C' => by
      change resG _ _ _ = resG Z.X _ 1 * resG _ _ _
      rw [map_one, one_mul, resG_resG, resG_resG]
      by_cases h : C = C'
      · subst h; rfl
      · have e : Z.gen ⊓ (compLB Z).U C ⊓ (compLB Z).U C' = ⊥ := eq_bot_iff.2 fun x hx =>
          (h (Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents C.2 C'.2 hx.1.2 hx.2))).elim
        have : Subsingleton Γ(Z.X, Z.gen ⊓ (compLB Z).U C ⊓ (compLB Z).U C') := by
          rw [e]; infer_instance
        exact Subsingleton.elim _ _

theorem vRes_compPair (g : Z.Comp → O) (hg : ∀ C, g C ≠ 0) (C : Z.Comp) :
    Z.vRes C (compPair g hg).cls = (Z.comp C).div (g C) (hg C) := by
  rw [vRes_cls, ← VertDiv.cls_const, ← add_zero (VertDiv.const _ _ _).cls, ← VertDiv.cls_zero]
  refine VertDiv.IsSum.cls_eq fun i j k => ⟨1, ?_⟩
  by_cases h : k ⟨⟩ = C
  · rw [VPair.eqn_pull _ (Z.compι_str C) k _ le_rfl
      (inf_le_inf (preimage_gen (Z.compι_str C)).ge (inf_le_right.trans (LB.pull_U_le _ k)))]
    change ((Z.compι C).appLE _ _ _).hom (resG _ _ (resG _ _ _)) = resG _ _ 1 * (resG _ _ (resG _ _ _) * resG _ _ 1)
    rw [map_one, map_one, one_mul, mul_one, resG_resG, resG_resG, LB.appLE_resG, ← appTop_const (Z.compι_str C)]
    exact (congrArg (fun A => ((Z.compι C).appLE ⊤ _ le_top).hom (Z.const (g A))) h).trans rfl
  · have e : (Z.comp C).gen ⊓ ((VertDiv.const _ (g C) (hg C)).M.U i ⊓ (VertDiv.zero _).M.U j ⊓
        ((compPair g hg).pull (Z.compι_str C)).M.U k) = ⊥ := eq_bot_iff.2 fun x hx =>
      (h (Subtype.ext (IsNormalScheme.eq_of_mem_irreducibleComponents (k ⟨⟩).2 C.2 (LB.pull_U_le _ k hx.2.2) x.2))).elim
    have : Subsingleton Γ((Z.comp C).X, (Z.comp C).gen ⊓ ((VertDiv.const _ (g C) (hg C)).M.U i ⊓ (VertDiv.zero _).M.U j ⊓
        ((compPair g hg).pull (Z.compι_str C)).M.U k)) := by
      rw [e]; infer_instance
    exact Subsingleton.elim _ _

theorem exists_vRes_eq_zero {C C' : Z.Comp} (h : C ≠ C') : ∃ D : Z.VDivZ, Z.vRes C D ≠ 0 ∧ Z.vRes C' D = 0 := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hg (A : Z.Comp) : (if A = C then ϖ else 1) ≠ 0 := by split_ifs; exacts [hϖ.ne_zero, one_ne_zero]
  refine ⟨(compPair _ hg).cls, ?_, ?_⟩
  · rw [vRes_compPair]
    exact Check.div_ne_zero _ (by rw [if_pos rfl]; exact hϖ.not_isUnit)
  · rw [vRes_compPair]
    exact Model.div_of_isUnit _ (by rw [if_neg h.symm]; exact isUnit_one) _

section Theory

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

theorem capDeg_divP_cD (d : ℕ) (D : (Z.toITh p d).VDiv) (Q : (Z.toITh p d).Ch) :
    (Z.toITh p d).capDeg (Z.toITh p d).divP ((Z.toITh p d).cD D * Q) = 0 :=
  (capDeg_vp_symm p d _ D Q).trans (by
    rw [show Z.cDQ (Z.toITh p d).divP = 0 from (Z.toITh p d).cD_divP, zero_mul, map_zero])

def smulPair (d : ℕ) (L : FinLB Z.X) : Formalism.BasicNotions.DV.FPair (Z.toITh p d) 1 :=
  ⟨fun _ => L, fun _ => L, fun _ => Z.vdiv L L (.smul L.isLB p (natCast_ne_zero O p)),
    fun _ => NModel.firstChern_eq_sub_divisor _ _ _⟩

variable (O) in

theorem ck_copies (n : ℕ) :
    Formalism.BasicNotions.DV.ck (smulPair (Z := copies O n 1) p 1 (twistingSheafOnCopies O n 1)) 1 (twistingSheafOnCopies O n 1).c1 = n ∧
    Formalism.BasicNotions.DV.ck (smulPair (Z := copies O n 1) p 1 (twistingSheafOnCopies O n 1)) 2 1 = 2 * n := by
  have h := capDeg_divP_copies O n 0 p
  have e : (copies O n 1).vdiv _ _ (.smul (twistingSheafOnCopies O n 1).isLB p (natCast_ne_zero O p)) =
    ((copies O n 1).toITh p 1).divP := vdiv_smul _ _ _
  simp only [zero_add, pow_one] at h
  simp only [Formalism.BasicNotions.DV.ck, Formalism.BasicNotions.DV.Gk, smulPair, Fin.sum_univ_one, Finset.sum_range_succ,
    Finset.sum_range_zero, e, pow_zero, pow_one, one_mul, mul_one, zero_add, Nat.sub_self, Nat.reduceSub, map_add, h]
  exact ⟨trivial, by ring⟩

theorem capDeg_empty [IsEmpty Z.X] (d : ℕ) (D : (Z.toITh p d).VDiv) (Q : (Z.toITh p d).Ch) :
    (Z.toITh p d).capDeg D Q = 0 := by
  have : IsEmpty Z.Comp := ⟨fun C => isEmptyElim C.2.1.1.some⟩
  exact (capDeg_vp_eq_sum p d D Q).trans (by simp)

variable (O) in

def mixed : NModel O :=
  haveI := fun i : Fin 2 => Model.isNormalScheme_projSpace O (i + 1)
  sigma fun i : Fin 2 => Model.projSpace O (i + 1)

variable (O) in

theorem capDeg_mixed (i : Fin 2) (x : PicSym (mixed O).X) :
    ((mixed O).toITh p (i + 1)).capDeg ((mixed O).toITh p (i + 1)).divP x =
      ((Model.projSpace O (i + 1)).toITh p).capDeg ((Model.projSpace O (i + 1)).toITh p).divP
        (picSymPull (Sigma.ι (fun i : Fin 2 => (Model.projSpace O (i + 1)).X) i) x) := by
  rw [capDeg_vp_toQ, Model.capDeg_vp_toQ, divP, vDeg_div_of_cover (Z := mixed O)
    (B := fun i : Fin 2 => Model.projSpace O (i + 1))
    (fun i => Sigma.ι (fun i : Fin 2 => (Model.projSpace O (i + 1)).X) i) (fun i => Sigma.ι_desc _ _)
    (fun x => (sigmaOpenCover _).exists_eq x)
    (fun i j ⟨x, hi, hj⟩ => by_contra fun hij => Set.disjoint_left.1
      (Opens.coe_disjoint.2 (disjoint_opensRange_sigmaι _ i j hij)) hi hj)]
  rw [Finset.sum_eq_single i]
  · rfl
  · intro j hj hji
    exact absurd (Fin.ext (by simpa using hj)) hji
  · simp

end Theory

section Mdl

open NumberField GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (M : Mdl Y i₀) (d : ℕ)

theorem capDeg_ithOf_symm (D D' : (ithOf hp hW M d).VDiv) (Q : (ithOf hp hW M d).Ch) :
    (ithOf hp hW M d).capDeg D ((ithOf hp hW M d).cD D' * Q) =
      (ithOf hp hW M d).capDeg D' ((ithOf hp hW M d).cD D * Q) :=
  haveI := isDiscreteValuationRing_V M.i.c hp hW
  capDeg_vp_symm (Z := nmodel M) p d D D' Q

theorem divisorOfPrime_ne_zero [Nonempty M.X] :
    haveI := Fact.mk hp
    haveI := isDiscreteValuationRing_V M.i.c hp hW
    (nmodel M).divP p ≠ 0 := fun h => by
  haveI := Fact.mk hp
  haveI := isDiscreteValuationRing_V M.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits M.i.c hp hW
  obtain ⟨C, -⟩ := (nmodel M).exists_comp (Classical.arbitrary M.X)
  have := congrArg ((nmodel M).vRes C) h
  rw [divP, vRes_div, map_zero] at this
  exact Check.div_ne_zero _ (natCast_mem_maximalIdeal _ p) this

end Mdl

end GlobalTheory.ShFam.Pad.IthCheck
