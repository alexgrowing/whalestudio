import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ProjSpace GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Points
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.TautFlag

theorem detUnit_chartSec_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j : L.ι) :
    (isFrame_chartSec hL i).detUnit (isFrame_chartSec hL j) inf_le_left inf_le_right = L.g i j := by
  refine (Units.ext ?_ : L.g i j = _).symm
  have e : resM (toMod L) inf_le_right (LB.chartSec hL j) = (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
      (isFrame_chartSec hL i).basis (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) 0 := by
    rw [IsFrame.basis_apply]
    refine ((LB.chartEquiv hL i inf_le_left).symm_apply_apply _).symm.trans ?_
    rw [LB.chartEquiv_symm_apply, LB.chartEquiv_apply]
    congr 1
    exact (resG_resG _ _ _).trans ((resG_resG _ _ _).trans (resG_self _ _))
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    e, map_smul, Module.Basis.repr_self]
  simp

theorem detUnit_eq_g_of_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X.Modules} (φ : F ≅ toMod L)
    (i j : L.ι) {e : Fin 1 → Γ(F, L.U i)} {f : Fin 1 → Γ(F, L.U j)} (h : IsFrame e) (k : IsFrame f)
    (he : e = fun _ => φ.inv.app _ (LB.chartSec hL i)) (hf : f = fun _ => φ.inv.app _ (LB.chartSec hL j)) :
    h.detUnit k inf_le_left inf_le_right = L.g i j := by
  subst he hf
  exact (IsFrame.detUnit_map_iso (isFrame_chartSec hL i) (isFrame_chartSec hL j) φ.inv _ _).trans
    (detUnit_chartSec_eq hL i j)

theorem adapt₁_quot_e (j : Fin 2) : (adapt₁ j).quot.e = fun _ => (grIso₁ seq seq_shortExact isVB_seq₁
    (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))).inv.app _ (LB.chartSec (O1_isLB ℤ 1) j) := by
  have e : (VMetric.stepSeq flag 1).g = quotMap ≫ (grIso₁ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
    (isVB_toMod (O1_isLB ℤ 1))).inv := (Iso.eq_comp_inv _).2 π_grIso₁
  funext _
  exact (congrArg (fun φ => φ.app _ (t j)) e).trans ((app_app _ _ _ _).symm.trans (congrArg _ (quotMap_app_t_eq_chartSec j)))

theorem g_adapt₁_quot (j j' : Fin 2) :
    (VB.det (flag.gr 1) 1).g (adapt₁ j).quot (adapt₁ j').quot = (O1 ℤ 1).g j j' :=
  detUnit_eq_g_of_iso (O1_isLB ℤ 1) _ j j' _ _ (adapt₁_quot_e j) (adapt₁_quot_e j')

variable {σ : ℤ →+* ℂ}

theorem nsqV_eq_one_add (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) : nsqV j y = ((1 + ‖ipVT j y‖ ^ 2 : ℝ) : ℂ) := by
  rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
  · have r : ev _ σ _ (ratio ℤ 1 0 0) y = 1 := by rw [ev_eq hy, ratio, ratioOn_self, map_one]
    rw [nsqV, r, map_one, mul_one, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one]
    rfl
  · have r : ev _ σ _ (ratio ℤ 1 1 1) y = 1 := by rw [ev_eq hy, ratio, ratioOn_self, map_one]
    rw [nsqV, r, map_one, mul_one, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one,
      add_comm, ← norm_neg]
    rfl

theorem det_quotGram_one_add (b : ℂ) :
    (quotGram (Matrix.fromBlocks (Matrix.of fun (_ _ : Fin 1) => ((1 + ‖b‖ ^ 2 : ℝ) : ℂ))
      (Matrix.of fun (_ _ : Fin 1) => b) (Matrix.of fun (_ _ : Fin 1) => starRingEnd ℂ b) 1)).det =
      (((1 + ‖b‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h : ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have e : starRingEnd ℂ b * b = ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) - 1 := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  rw [Complex.ofReal_inv]
  generalize ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) = n at h e
  simp only [quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply, Matrix.inv_subsingleton, Fintype.sum_unique]
  simp
  field_simp
  linear_combination -e

theorem fubini_study_weight_chart_eq (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((hermitianTwistingSheaf ℤ 1).φ σ).φ j y = Real.log (1 + ‖ipVT j y‖ ^ 2) := by
  refine (Weight.fsBasis_φ _ _ (iSup_nonzeroLocus_coord ℤ 1) 1 (by simp) _ _).trans (congrArg _ ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Fin.sum_univ_two _).trans (Complex.ofReal_injective (Eq.trans ?_ (nsqV_eq_one_add j hy)))
  rw [nsqV, Complex.mul_conj', Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow]
  rfl

theorem isometric_grLB_one : (VMetric.grLB flag 1 stdH.cInf).Isometric (hermitianTwistingSheaf ℤ 1) := by
  refine HermLB.Isometric.symm (HermLB.isometric_of_chart (L := hermitianTwistingSheaf ℤ 1) (M := VMetric.grLB flag 1 stdH.cInf)
    (fun j : Fin 2 => (adapt₁ j).quot) (fun _ => le_rfl)
    (fun x j j' _ _ => congrArg (gm (𝟙 _) x _) (g_adapt₁_quot j j').symm) fun σ j y hy => ?_)
  have e := ((stdH.h.stepMet flag 1).met σ).quot_G (VMetric.stepSeq_shortExact flag 1)
    (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) (adapt₁ j) hy
  have e₂ := e.trans (congrArg quotGram (gram_adapt₁ j hy))
  refine (congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => -Real.log M.det.re) e₂).trans
    (Eq.trans ?_ (fubini_study_weight_chart_eq j hy).symm)
  beta_reduce
  rw [nsqV_eq_one_add j hy, det_quotGram_one_add, Complex.ofReal_re, Real.log_inv, neg_neg]

end GlobalTheory.TautFlag
