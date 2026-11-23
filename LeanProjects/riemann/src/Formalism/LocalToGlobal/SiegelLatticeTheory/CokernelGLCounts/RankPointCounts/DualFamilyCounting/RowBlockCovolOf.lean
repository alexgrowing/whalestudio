import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RealCovolume
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PjRowPars
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.TraceReHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowRankHolds

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.RealCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gR {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : ℝ :=
  if c.val < D.R.k then 1 else -(1 / Formalism.L2.SG.RealObj.Tw u)

theorem gC_eq {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : gC u c = ((gR u c : ℝ) : ℂ) := by
  unfold gC gR; split_ifs <;> push_cast <;> rfl

theorem perp_aaLbS {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {x : (VS D).V} (hx : x ∈ aaLbS X b) (a : Fin D.R.rS) :
    (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, -, l, hl, rfl⟩ := hy
    obtain ⟨h1, h2⟩ := X.Lb_perp l hl a
    exact ⟨by rw [map_smul, h1, smul_zero], by rw [map_smul, h2, smul_zero]⟩
  | zero => exact ⟨map_zero _, map_zero _⟩
  | add y z _ _ hy hz => exact ⟨by rw [map_add, hy.1, hz.1, add_zero], by rw [map_add, hy.2, hz.2, add_zero]⟩
  | smul c y _ hy =>
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E c y, map_smul, hy.1, smul_zero]
    · rw [← algebraMap_smul D.host.E c y, map_smul, hy.2, smul_zero]

theorem gR_ne {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : gR u c ≠ 0 := by
  have hT := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  unfold gR; split_ifs
  · exact one_ne_zero
  · simp only [ne_eq, neg_eq_zero, one_div, inv_eq_zero]; exact hT.ne'

theorem prod_gR {D : D7} (u : D.what₂.Word) : ∏ c : Fin (D.R.k + 1), |gR u c| = 1 / Formalism.L2.SG.RealObj.Tw u := by
  have hT := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  rw [Fin.prod_univ_castSucc]
  have h1 : ∀ i : Fin D.R.k, |gR u (Fin.castSucc i)| = 1 := fun i => by
    unfold gR; rw [if_pos (by simp)]; simp
  have h2 : |gR u (Fin.last D.R.k)| = 1 / Formalism.L2.SG.RealObj.Tw u := by
    unfold gR; rw [if_neg (by simp)]; rw [abs_neg, abs_of_pos (by positivity)]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_const_one, one_mul, h2]

theorem Qf_rowV {D : D7} (X : HidaSetting D) (u : D.what₂.Word) {x y : (VS D).V}
    (hx : ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0)
    (hy : ∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) :
    Qf (gR u) (rowV X u x) (rowV X u y) = ((Algebra.trace ℚ D.host.E ((VS D).hT x y) : ℚ) : ℝ) / 2 := by
  rw [← traceRe_holds X]
  unfold Qf
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← rowParseval_holds X u x y hx hy v, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [gC_eq, Complex.re_mul_ofReal]

theorem rowBlockCovol_of (hT : TrDetUnimod) : RowBlockCovol := by
  intro D X u b
  classical
  obtain ⟨m⟩ := CovolumeSpans.rowRank_holds X b
  set N := Module.finrank ℚ D.host.E * (D.R.k + 1) with hNdef
  set w : Fin N → (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) := fun i => rowV X u (m i : (VS D).V) with hw
  have hmem : ∀ i, ((m i : (VS D).V)) ∈ aaLbS X b := fun i => (m i).2

  have hcl : cLat X u (Sum.inl (Sum.inr b)) = AddSubgroup.closure (Set.range w) := by
    show AddSubgroup.closure (rowV X u '' aaLb X b) = _
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ (aaLbS X b).restrictScalars ℤ := hx
      have hsum := m.sum_repr ⟨x, hx'⟩
      have e : x = ∑ i, (m.repr ⟨x, hx'⟩ i) • (m i : (VS D).V) := by
        have := congrArg Subtype.val hsum
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
        exact this.symm
      rw [e]
      have : rowV X u (∑ i, (m.repr ⟨x, hx'⟩ i) • (m i : (VS D).V)) =
          ∑ i, (m.repr ⟨x, hx'⟩ i) • w i := by
        have h := map_sum (Formalism.L2.SG.Pf.NcReal.JX.NOf.rowHom X u)
          (fun i => (m.repr ⟨x, hx'⟩ i) • (m i : (VS D).V)) Finset.univ
        simp only [map_zsmul] at h
        exact h
      rw [SetLike.mem_coe, this]
      exact AddSubgroup.sum_mem _ fun i _ =>
        AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact AddSubgroup.subset_closure ⟨(m i : (VS D).V), hmem i, rfl⟩

  have hQ : (Matrix.of fun i j => Qf (gR u) (w i) (w j)) =
      (1 / 2 : ℝ) • (Matrix.of fun i j =>
        (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).map (Rat.castHom ℝ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, hw, smul_eq_mul]
    change _ = 1 / 2 * (((Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))) : ℚ) : ℝ)
    rw [Qf_rowV X u (perp_aaLbS X b (hmem i)) (perp_aaLbS X b (hmem j))]
    ring
  have hTr := hT X b m rfl
  have hdE : (discr D.host.E : ℚ) ≠ 0 := by exact_mod_cast discr_ne_zero D.host.E
  have hNa : (FractionalIdeal.absNorm (aaD D b) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact aaD_ne_zero X b
  have hdetQ : (Matrix.of fun i j =>
      (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).det ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hTr
    exact (mul_ne_zero (pow_ne_zero _ (abs_ne_zero.2 hdE)) (pow_ne_zero _ hNa)) hTr.symm
  have hdetG : (Matrix.of fun i j => Qf (gR u) (w i) (w j)).det =
      (1 / 2 : ℝ) ^ N * (((Matrix.of fun i j =>
        (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).det : ℚ) : ℝ) := by
    rw [hQ, Matrix.det_smul, Fintype.card_fin]
    congr 1
    exact (RingHom.map_det (Rat.castHom ℝ) _).symm
  have hdet : (Matrix.of fun i j => Qf (gR u) (w i) (w j)).det ≠ 0 := by
    rw [hdetG]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hdetQ)
  have hcard : Fintype.card (InfinitePlace X.B.I.F × Fin (D.R.k + 1) × Fin 2) = N := by
    rw [Fintype.card_prod, Fintype.card_prod, card_ι X, Fintype.card_fin, Fintype.card_fin, hNdef,
      ← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    ring
  obtain ⟨h1, h2, h3⟩ := covol_of_gram w (gR u) (gR_ne u) hcard hdet
  rw [hcl]
  refine ⟨h1, h2, fun F hF hFd => ?_⟩
  change (volume : Measure (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ)) F = _
  rw [h3 F hF hFd]
  congr 1

  set dF : ℝ := |(discr X.B.I.F : ℝ)| with hdF
  have hdF0 : 0 < dF := dF_pos X
  set fC : ℕ := Fintype.card (InfinitePlace X.B.I.F) with hfC
  set T : ℝ := Formalism.L2.SG.RealObj.Tw u with hTdef
  have hT0 : 0 < T := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hNf : N = 2 * (fC * (D.R.k + 1)) := by
    rw [← hcard, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
  set x : ℝ := -(2 * ((D.R.rS : ℝ) - (b : ℕ))) with hx
  have hTrR : |(((Matrix.of fun i j =>
      (Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)))).det : ℚ) : ℝ)| =
      (dF ^ 2) ^ (D.R.k + 1) * (dF ^ x) ^ (2 * (D.R.k + 1)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hTr
    simp only [Rat.cast_abs, Rat.cast_mul, Rat.cast_pow] at h
    rw [h, ← absDiscrE X, absNorm_aaD X b]
    push_cast; rfl
  have hsq : |(Matrix.of fun i j => Qf (gR u) (w i) (w j)).det| =
      ((1 / 2 : ℝ) ^ (fC * (D.R.k + 1)) * dF ^ (D.R.k + 1) * (dF ^ x) ^ (D.R.k + 1)) ^ 2 := by
    rw [hdetG, abs_mul, hTrR, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hNf]
    ring
  have hnn : 0 ≤ (1 / 2 : ℝ) ^ (fC * (D.R.k + 1)) * dF ^ (D.R.k + 1) * (dF ^ x) ^ (D.R.k + 1) := by positivity
  rw [hsq, Real.sqrt_sq hnn]
  have hprod : ∏ v : InfinitePlace X.B.I.F, ∏ c : Fin (D.R.k + 1), |gR u c| = (1 / T) ^ fC := by
    simp only [prod_gR, Finset.prod_const, Finset.card_univ]; rfl
  rw [hprod]
  show _ = T ^ fC * (2 : ℝ)⁻¹ ^ (fC * (D.R.k + 1)) *
    dF ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ))))
  have hexp : dF ^ (D.R.k + 1) * (dF ^ x) ^ (D.R.k + 1) =
      dF ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ)))) := by
    rw [← Real.rpow_natCast dF, ← Real.rpow_natCast (dF ^ x), ← Real.rpow_mul hdF0.le, ← Real.rpow_add hdF0]
    congr 1; rw [hx]; push_cast; ring
  have hTinv : ((1 / T) ^ fC)⁻¹ = T ^ fC := by rw [one_div, inv_pow, inv_inv]
  rw [mul_assoc, hexp, div_eq_mul_inv, hTinv]
  ring

end Formalism.L2.SG.Pf.NcReal.JX.CovB
