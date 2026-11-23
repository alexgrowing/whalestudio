import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace LelongRegularise

theorem mdisc_eq_zero_of_eq_zero {D : ℕ} (B : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (h : B 0 = 0) : ReciprocityTheory.AnForm.mdisc B = 0 := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  refine mul_eq_zero_of_right _ ?_
  have hu : (Finset.univ : Finset (Fin (D + 1))) = insert 0 (Finset.univ.erase 0) :=
    (Finset.insert_erase (Finset.mem_univ 0)).symm
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert (Finset.notMem_erase 0 _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht => ?_
  have h0t : (0 : Fin (D + 1)) ∉ t := fun h0 => Finset.notMem_erase 0 _ (Finset.mem_powerset.1 ht h0)
  have hc : t.card ≤ D := by
    have := Finset.card_le_card (Finset.mem_powerset.1 ht)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [Finset.sum_insert h0t, h, zero_add, Finset.card_insert_of_notMem h0t]
  have he : D + 1 - t.card = (D + 1 - (t.card + 1)) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem maDens_eq_zero_of_eventually {D : ℕ} (F : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    {y : Fin (D + 1) → ℂ} (h : F 0 =ᶠ[𝓝 y] fun _ => 0) : ReciprocityTheory.AnForm.maDens F y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ (F 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    simp
  have hH : ReciprocityTheory.AnForm.hessC (F 0) y = 0 := by
    ext i j
    simp [ReciprocityTheory.AnForm.hessC, h2]
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_eq_zero_of_eq_zero (fun k => ReciprocityTheory.AnForm.hessC (F k) y) hH]
  simp

theorem abs_half_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (t ^ 2 + ε) / 2| ≤ |Real.log t| + |Real.log (2 * t)| := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hlo : Real.log t ≤ Real.log (t ^ 2 + ε) / 2 := by
    have : Real.log (t ^ 2) ≤ Real.log (t ^ 2 + ε) := Real.log_le_log ht2 (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hup : Real.log (t ^ 2 + ε) ≤ 2 * (|Real.log t| + |Real.log (2 * t)|) := by
    have h1 : Real.log (t ^ 2 + ε) ≤ Real.log (t ^ 2 + 1) := Real.log_le_log (by positivity) (by linarith)
    have h2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht.ne'
    rcases le_total t 1 with h | h
    · have : Real.log (t ^ 2 + 1) ≤ Real.log (2 ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := neg_abs_le (Real.log t)
      linarith
    · have : Real.log (t ^ 2 + 1) ≤ Real.log ((2 * t) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := abs_nonneg (Real.log t)
      linarith
  rw [abs_le]
  constructor
  · have a1 := neg_abs_le (Real.log t)
    have a2 := abs_nonneg (Real.log (2 * t))
    linarith
  · linarith

theorem tendsto_logReg {n : ℕ} (u x : Fin n → ℂ) (hx : linEval u x ≠ 0) :
    Tendsto (fun ε => logReg u ε x) (𝓝[>] 0) (𝓝 (Real.log ‖linEval u x‖)) := by
  rw [← logReg_zero]
  have hc : ContinuousAt (fun ε => logReg u ε x) 0 := by
    unfold logReg
    refine ContinuousAt.div_const (ContinuousAt.log (continuousAt_const.add continuousAt_id) ?_) _
    simp [hx]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem exists_poly_of_linEval_eq_zero {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ y x, x ∈ fibre J A y → linEval u x = 0 → MvPolynomial.eval y P = 0 := by
  classical
  have := hJ
  set a := Ideal.Quotient.mk J (linForm u) with ha_def
  have ha : a ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hint : (projHom J A).toRingHom.IsIntegralElem a := hA.finite.to_isIntegral _
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom a = 0 := by
    obtain ⟨p, hpm, hp⟩ := hint
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  refine ⟨p.coeff 0, fun h0 => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hq : q.eval₂ (projHom J A).toRingHom a = 0 := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
      exact (mul_eq_zero.1 hp).resolve_left ha
    have hlt : q.natDegree < Nat.find hex := by
      rw [← hpk, Polynomial.natDegree_X_mul hqm.ne_zero]
      omega
    exact Nat.find_min hex hlt ⟨q, hqm, rfl, hq⟩
  · rintro y x ⟨hx, hxy⟩ hux
    have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) hp
    rw [Polynomial.hom_eval₂, IndefiniteRowSideFullHecke.ComplexSets.lift_eval_comp_projHom J A hx, map_zero] at h
    have hax : (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) a = 0 := by
      rw [ha_def, Ideal.Quotient.lift_mk, ← hux]
      simp [linForm, linEval]
    rw [hax, Polynomial.eval₂_at_zero, hxy] at h
    exact h

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : ι → ℂ, MvPolynomial.eval w g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖w‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm w i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r)
    (fun w => MvPolynomial.eval w g ≠ 0)).mpr fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem norm_chartDens_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (logReg u ε) (vecCons f φ) y‖ ≤
      chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖)
          (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h2 : ‖linEval ((2 : ℂ) • u) x‖ = 2 * ‖linEval u x‖ := by
        have : linEval ((2 : ℂ) • u) x = 2 * linEval u x := by
          simp [linEval, Finset.mul_sum, mul_assoc]
        rw [this, norm_mul]
        norm_num
      rw [h2]
      exact abs_half_log_le (norm_pos_iff.2 (hy x hx)) hε hε1
    · have hM : ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ hs.choose) y = 0 := by
        obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs.choose_spec
        refine maDens_eq_zero_of_eventually _ ?_
        have hc : ContinuousAt hs.choose y := by
          rw [← hx.2]
          exact hsd.continuousOn.continuousAt (hU.mem_nhds hxU)
        have hx' : x ∉ tsupport f := fun h => hxB (hR h)
        have hn : (tsupport f)ᶜ ∈ 𝓝 (hs.choose y) := by
          rw [← hx.2, hsx]
          exact (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
        filter_upwards [hc.preimage_mem_nhds hn] with w hw
        simp only [Matrix.cons_val_zero, Function.comp_apply]
        exact image_eq_zero_of_notMem_tsupport hw
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp

theorem tendsto_chartDens {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (logReg u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y)) := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine tendsto_finsetSum _ fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    exact (tendsto_logReg u x (hy x hx)).mul_const _
  · simp only [dif_neg hs]
    exact tendsto_const_nhds

end LelongRegularise

theorem LelongRegularise.proof (h : LogIntegrable.Statement) : LelongRegularise.Statement := by
  intro n d J u f φ hJ hdim hu hf hfc hφ
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  have hAf := hA.choose_spec
  unfold chartInt
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hf
    · simpa using hφ i
  have hu2 : linForm ((2 : ℂ) • u) ∉ J := by
    have he : linForm ((2 : ℂ) • u) = C 2 * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, C_mul]
    intro hm
    apply hu
    have := J.mul_mem_left (C (1 / 2 : ℂ)) (he ▸ hm)
    rwa [← mul_assoc, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1, one_mul] at this
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hAf hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J hA.choose y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx h0
    exact hy (hPy y x hx h0)
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
    ((h n (d + 1) J hA.choose u (vecCons f φ) R hJ hdim hAf hu hψ).add
      (h n (d + 1) J hA.choose ((2 : ℂ) • u) (vecCons f φ) R hJ hdim hAf hu2 hψ)) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (SheetSumMeasurable.proof n (d + 1) J hA.choose (logReg u ε) (vecCons f φ) hJ hdim hAf
      (contDiff_logReg u hε).continuous.measurable hψ).1.aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hgood] with y hy
    exact LelongRegularise.norm_chartDens_le hAf φ hR hε.1 hε.2 hy
  · filter_upwards [hgood] with y hy
    exact LelongRegularise.tendsto_chartDens hAf _ hy

end

end GroundTheory.Heights₂.Heights
