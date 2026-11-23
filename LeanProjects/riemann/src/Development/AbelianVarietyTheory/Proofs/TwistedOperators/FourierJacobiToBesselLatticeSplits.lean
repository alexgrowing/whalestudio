import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLattiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.SplitsFB

theorem inv_neg_mat {D : D7} {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplO_negSp {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have e : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem symplO_zero_left' {D : D7} (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  unfold symplO hO
  simp

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sd_grid (i : ℕ) (h1 : 1 ≤ i) (h : i ≤ D.R.m) : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
  (G.isV (X := .grid i 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd

theorem latRow_mxAt (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u} (hu : u ∈ latRow G i) : MxAt (fun _ => True) u :=
  ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega)) (fun _ => True) u).1
    hu.1).1

theorem latRow_pair (W : G.Weil) (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u u'} (hu : u ∈ latRow G i) (hu' : u' ∈ latRow G i) :
    W.ψ (symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u') = 1 := by
  have := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega))
    (fun _ => True) u (latRow_mxAt G i h1 h hu)).1 hu.1 u' hu'.1
  rwa [symplO_negSp, AddChar.map_neg_eq_inv, inv_eq_one] at this

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {x : Mx D m n} (hx : MxAt P x) (y : Mx D n k) : MxAt P (x ⬝ y) :=
  fun i j => by
    show (x * y) i j ∈ _
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

end

set_option maxHeartbeats 2000000 in

theorem splits_FB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hS := GlobalTheory.T.depthLatticeGridRow_stable_witt_projections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hT := GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hC := GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hB := GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) (by omega)
  refine ⟨fun u hu => ?_⟩
  set dV := F.dJ (σ + 1) h with hdV
  set dW := F.dB σ h' with hdW
  obtain ⟨hX, hY⟩ := hS u hu
  have e1 := dV.sum_eq_one
  have e2 := dW.sum_eq_one
  have h0 : u ⬝ (dV.j0 ⬝ dV.p0) ∈ latRow G (2 * σ + 2) := by
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    have e : u ⬝ (dV.j0 ⬝ dV.p0) = u - u ⬝ (dV.jX ⬝ dV.pX) - u ⬝ (dV.jY ⬝ dV.pY) := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem hu hX) hY
  set w := u ⬝ (dV.j0 ⬝ dV.p0) with hw
  obtain ⟨gX, gY⟩ := hT w h0
  have g0 : (dW.j0 ⬝ dW.p0) ⬝ w ∈ latRow G (2 * σ + 2) := by
    have s : (dW.jX ⬝ dW.pX) ⬝ w + (dW.j0 ⬝ dW.p0) ⬝ w + (dW.jY ⬝ dW.pY) ⬝ w = w := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, e2, Matrix.one_mul]
    have e : (dW.j0 ⬝ dW.p0) ⬝ w = w - (dW.jX ⬝ dW.pX) ⬝ w - (dW.jY ⬝ dW.pY) ⬝ w := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem h0 gX) gY
  have hA1 : dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc]; exact hX
  have hA2 : dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extY_apply, Matrix.mul_assoc]; exact hY
  have hB1 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) = (dW.jX ⬝ dW.pX) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, hw]; simp only [Matrix.mul_assoc]
  have hB2 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) = (dW.jY ⬝ dW.pY) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, hw]; simp only [Matrix.mul_assoc]
  have hG0 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) = (dW.j0 ⬝ dW.p0) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, hw]; simp only [Matrix.mul_assoc]
  have heq : u = dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) + dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) +
      dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0)) + dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0)) +
        dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) := by
    rw [map_add, map_add, hB1, hB2, hG0, HypDec.extX_apply, HypDec.extY_apply, ← Matrix.add_mul, ← Matrix.add_mul,
      show dW.jX ⬝ dW.pX + dW.jY ⬝ dW.pY + dW.j0 ⬝ dW.p0 = 1 from (add_right_comm _ _ _).trans e2, Matrix.one_mul, hw,
      Matrix.mul_assoc, Matrix.mul_assoc]
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    conv_lhs => rw [← s]
    abel
  refine ⟨u ⬝ dV.jX, hA1, u ⬝ dV.jY, AddSubgroup.subset_closure
      ⟨mxAt_mul (latRow_mxAt G (2 * σ + 2) (by omega) (by omega) hu) _,
        fun a ha => latRow_pair G W (2 * σ + 2) (by omega) (by omega) ha hA2⟩,
    dW.pX ⬝ (u ⬝ dV.j0), ?_, dW.pY ⬝ (u ⬝ dV.j0), ?_, dW.p0 ⬝ (u ⬝ dV.j0), ?_, heq, hC _ hA2, ?_⟩
  · show dV.ext0 _ (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB1]; exact hB gX
  · show dV.ext0 _ (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB2]; exact hB gY
  · show dV.ext0 _ (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) ∈ latRow G (2 * σ + 2)
    rw [hG0]; exact g0
  · rw [map_zero, symplO_zero_left', AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.SplitsFB
