import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffC

noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

def ell (β : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((2 * Real.pi * Complex.I) • ((Matrix.traceLinearMap (Fin n) ℂ ℂ).comp (LinearMap.mulLeft ℂ β)))

theorem ell_apply (β H : Matrix (Fin n) (Fin n) ℂ) : ell β H = 2 * Real.pi * Complex.I * (β * H).trace := by
  simp [ell]

theorem eTr_eq (β : Matrix (Fin n) (Fin n) ℂ) (x : Vr n) : eTr β x = Complex.exp (ell β (herm x)) := by
  simp [eTr, ell_apply]

theorem trace_mul_single' (β : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n) :
    (β * Matrix.single r c 1).trace = β c r := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem dList_exp (β : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (l : List (Fin n × Fin n)) (c : ℂ) (x : Vr n),
      dList l (fun y => c * Complex.exp (ell β (herm y))) x =
        c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod * Complex.exp (ell β (herm x))
  | [], c, x => by simp [dList]
  | a :: l, c, x => by
    have h : dList l (fun y => c * Complex.exp (ell β (herm y))) =
        fun y => (c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod) * Complex.exp (ell β (herm y)) := by
      funext y; rw [dList_exp β l c y]
    simp only [dList]
    rw [h]
    set c' := c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod
    have hd : HasFDerivAt (fun H => c' * Complex.exp (ell β H))
        (c' • (Complex.exp (ell β (herm x)) • ell β)) (herm x) :=
      ((ell β).hasFDerivAt.cexp).const_mul c'
    rw [dc_comp hd.differentiableAt, hd.fderiv]
    simp only [_root_.smul_apply, smul_eq_mul, List.map_cons, List.prod_cons, c']
    ring

def ml (σ : Equiv.Perm (Fin n)) : Fin (Fintype.card (Fin n)) → Fin n × Fin n :=
  fun i => ((Fintype.equivFin (Fin n)).symm i, σ ((Fintype.equivFin (Fin n)).symm i))

theorem sum_sign_prod_ell (β : Matrix (Fin n) (Fin n) ℂ) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod =
      (2 * Real.pi * Complex.I) ^ Fintype.card (Fin n) * β.det := by
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, ml, ell_apply, trace_mul_single', Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (∏ i : Fin (Fintype.card (Fin n)), β (σ ((Fintype.equivFin (Fin n)).symm i))
      ((Fintype.equivFin (Fin n)).symm i)) = ∏ a : Fin n, β (σ a) a from
    Fintype.prod_equiv (Fintype.equivFin (Fin n)).symm _ _ (fun _ => rfl)]
  rw [Units.smul_def, zsmul_eq_mul]
  push_cast
  ring

theorem fourier_test (β : Matrix (Fin n) (Fin n) ℂ) (hdet : β.det = 0) {φ : Vr n → ℂ} (hφ : IsT Set.univ φ) :
    ∫ x, (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) * eTr β x = 0 := by
  set E : Vr n → ℂ := fun y => 1 * Complex.exp (ell β (herm y)) with hE
  have hEs : ContDiffOn ℝ ∞ E Set.univ := by
    refine (contDiff_const.mul ?_).contDiffOn
    exact Complex.contDiff_exp.comp (((ell β).restrictScalars ℝ).contDiff.comp (hermL n).contDiff)
  have hT : ∀ σ : Equiv.Perm (Fin n), IsT Set.univ (dList (List.ofFn (ml σ)).reverse φ) := fun σ => isT_dList hφ _
  have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => E x * dList (List.ofFn (ml σ)).reverse φ x) :=
    fun σ => integrable_mul_of_contOn isOpen_univ hEs.continuousOn (hT σ).smooth.continuous (hT σ).cpt
      (Set.subset_univ _)
  have h1 : (fun x => (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) *
      eTr β x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
        (E x * dList (List.ofFn (ml σ)).reverse φ x) := by
    funext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun σ _ => ?_; rw [eTr_eq]; simp only [E]; ring
  rw [h1, integral_finsetSum _ (fun σ _ => (hint σ).const_mul _)]
  have h2 : ∀ σ : Equiv.Perm (Fin n), ∫ x, (Equiv.Perm.sign σ : ℂ) * (E x * dList (List.ofFn (ml σ)).reverse φ x) =
      (Equiv.Perm.sign σ : ℂ) * ((-1) ^ Fintype.card (Fin n) *
        (((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod *
          ∫ x, Complex.exp (ell β (herm x)) * φ x)) := by
    intro σ
    rw [integral_const_mul, ibp_dList isOpen_univ _ hEs hφ, List.reverse_reverse, List.length_reverse,
      List.length_ofFn]
    congr 2
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [E]
    rw [dList_exp β _ 1 x]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ)]
  have h3 : ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ((-1) ^ Fintype.card (Fin n) *
        (((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod *
          ∫ x, Complex.exp (ell β (herm x)) * φ x)) =
      (-1) ^ Fintype.card (Fin n) * (∫ x, Complex.exp (ell β (herm x)) * φ x) *
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          ((List.ofFn (ml σ)).map fun a => ell β (Matrix.single a.1 a.2 1)).prod := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
  rw [h3, sum_sign_prod_ell, hdet]
  ring

end STD

open STD in
theorem singToDiff : SingToDiff := by
  intro n G r hr hG hyp
  classical
  set U : Set (Vr n) := (hermL n) ⁻¹' Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball.preimage (hermL n).continuous
  have h0U : (0 : Vr n) ∈ U := by simp [U, hermL_apply, herm_zero, hr]
  set F : Vr n → ℂ := fun y => G (herm y) with hFdef
  have hF : ContDiffOn ℝ ∞ F U :=
    (hG.restrict_scalars ℝ).comp (hermL n).contDiff.contDiffOn (fun y hy => hy)
  let H : Vr n → ℂ := fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)) F x
  have hHU : ContinuousOn H U := by
    refine continuousOn_finsetSum _ fun σ _ => continuousOn_const.mul ?_
    exact (contDiffOn_dList hU hF _).continuousOn
  have hH0 : H 0 = detD G := by
    simp only [H, detD]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [dList_ofFn hG _ (ml σ) 0 (by simpa [herm_zero] using hr), herm_zero]
    rfl
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have key : ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : ContDiffBump (0 : Vr n), b.rOut = ε →
      ∫ x, H x * ((b.normed volume x : ℝ) : ℂ) = 0 := by
    intro ε hε hεε b hb
    set φ : Vr n → ℂ := fun x => ((b.normed volume x : ℝ) : ℂ) with hφdef
    have hφsup : tsupport φ ⊆ Metric.closedBall 0 ε := by
      refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
      have h1 : b.normed volume x ≠ 0 := fun h0 => hx (by simp [φ, h0])
      have hx' : x ∈ Function.support (b.normed volume) := h1
      rw [b.support_normed_eq, hb] at hx'
      exact Metric.ball_subset_closedBall hx'
    have hφ : IsT U φ := by
      refine ⟨Complex.ofRealCLM.contDiff.comp b.contDiff_normed, ?_, ?_⟩
      · exact b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
      · exact hφsup.trans ((Metric.closedBall_subset_ball hεε).trans hball)
    have hφu : IsT Set.univ φ := ⟨hφ.smooth, hφ.cpt, Set.subset_univ _⟩
    set ψ : Vr n → ℂ := fun x =>
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x with hψdef
    have hψT : ∀ σ : Equiv.Perm (Fin n), IsT U (dList (List.ofFn (ml σ)).reverse φ) := fun σ => isT_dList hφ _
    have hψ0 : ∀ x, x ∉ tsupport φ → ψ x = 0 := by
      intro x hx
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_dList_subset φ _ h)), mul_zero]
    have hSing : IsSingTest ψ := by
      refine ⟨continuous_finsetSum _ fun σ _ => continuous_const.mul (hψT σ).smooth.continuous,
        HasCompactSupport.intro hφ.cpt hψ0, ?_⟩
      intro β _ hdet
      exact fourier_test β hdet hφu
    have h1 := hyp ψ hSing
    have hint : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => F x * dList (List.ofFn (ml σ)).reverse φ x) :=
      fun σ => integrable_mul_of_contOn hU hF.continuousOn (hψT σ).smooth.continuous (hψT σ).cpt (hψT σ).sub
    have h2 : ∫ x, G (herm x) * ψ x = (-1) ^ Fintype.card (Fin n) * ∫ x, H x * φ x := by
      have e1 : (fun x => G (herm x) * ψ x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          (F x * dList (List.ofFn (ml σ)).reverse φ x) := by
        funext x; simp only [ψ, F, Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
      have hintH : ∀ σ : Equiv.Perm (Fin n), Integrable (fun x => dList (List.ofFn (ml σ)) F x * φ x) :=
        fun σ => integrable_mul_of_contOn hU (contDiffOn_dList hU hF _).continuousOn hφ.smooth.continuous
          hφ.cpt hφ.sub
      have e2 : (fun x => H x * φ x) = fun x => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
          (dList (List.ofFn (ml σ)) F x * φ x) := by
        funext x; simp only [H, Finset.sum_mul]; refine Finset.sum_congr rfl fun σ _ => ?_; ring
      rw [e1, e2, integral_finsetSum _ (fun σ _ => (hint σ).const_mul _),
        integral_finsetSum _ (fun σ _ => (hintH σ).const_mul _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [integral_const_mul, integral_const_mul, ibp_dList hU _ hF hφ, List.reverse_reverse, List.length_reverse,
        List.length_ofFn]
      ring
    rw [h2] at h1
    have hne : ((-1 : ℂ)) ^ Fintype.card (Fin n) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 h1).resolve_left hne

  rw [← hH0]
  by_contra hne
  have hδ : 0 < ‖H 0‖ / 2 := by positivity
  obtain ⟨ε1, hε1, hcont⟩ := Metric.continuousAt_iff.1 (hHU.continuousAt (hU.mem_nhds h0U)) _ hδ
  set ε := min (ε0 / 2) (ε1 / 2) with hεdef
  have hε : 0 < ε := lt_min (half_pos hε0) (half_pos hε1)
  have hεε0 : ε < ε0 := (min_le_left _ _).trans_lt (half_lt_self hε0)
  have hεε1 : ε < ε1 := (min_le_right _ _).trans_lt (half_lt_self hε1)
  let b : ContDiffBump (0 : Vr n) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hk := key ε hε hεε0 b rfl
  set φr : Vr n → ℝ := b.normed volume
  have hφr1 : ∫ x, φr x = 1 := b.integral_normed
  have hφint : Integrable φr := b.integrable_normed
  have hcpt : HasCompactSupport (fun x => ((φr x : ℝ) : ℂ)) := b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hφc : Continuous (fun x => ((φr x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp b.continuous_normed
  have hsub : tsupport (fun x => ((φr x : ℝ) : ℂ)) ⊆ U := by
    refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans
      ((Metric.closedBall_subset_ball hεε0).trans hball)
    have h1 : φr x ≠ 0 := fun h0 => hx (by simp [h0])
    have hx' : x ∈ Function.support φr := h1
    rw [b.support_normed_eq] at hx'
    exact Metric.ball_subset_closedBall hx'
  have hi1 : Integrable (fun x => H x * ((φr x : ℝ) : ℂ)) := integrable_mul_of_contOn hU hHU hφc hcpt hsub
  have hi2 : Integrable (fun x => (H 0 - H x) * ((φr x : ℝ) : ℂ)) :=
    integrable_mul_of_contOn hU (continuousOn_const.sub hHU) hφc hcpt hsub
  have hrep : H 0 = ∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ) := by
    have : ∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ) = H 0 * (∫ x, ((φr x : ℝ) : ℂ)) - ∫ x, H x * ((φr x : ℝ) : ℂ) := by
      have hA : Integrable (fun x => H 0 * ((φr x : ℝ) : ℂ)) :=
        integrable_mul_of_contOn hU continuousOn_const hφc hcpt hsub
      have e : (fun x => (H 0 - H x) * ((φr x : ℝ) : ℂ)) =
          fun x => H 0 * ((φr x : ℝ) : ℂ) - H x * ((φr x : ℝ) : ℂ) := by
        funext x; ring
      rw [e, integral_sub hA hi1, integral_const_mul]
    rw [this, hk, integral_complex_ofReal, hφr1]; simp
  have hbound : ‖∫ x, (H 0 - H x) * ((φr x : ℝ) : ℂ)‖ ≤ ∫ x, ‖H 0‖ / 2 * φr x := by
    refine norm_integral_le_of_norm_le (hφint.const_mul _) (Eventually.of_forall fun x => ?_)
    by_cases hx : φr x = 0
    · simp [hx]
    · have hx' : x ∈ Function.support φr := hx
      rw [b.support_normed_eq] at hx'
      have hd : dist x 0 < ε1 := (Metric.mem_ball.1 hx').trans hεε1
      have := hcont hd
      rw [dist_eq_norm, norm_sub_rev] at this
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b.nonneg_normed x)]
      exact mul_le_mul_of_nonneg_right this.le (b.nonneg_normed x)
  rw [integral_const_mul, hφr1, mul_one, ← hrep] at hbound
  have : ‖H 0‖ ≤ 0 := by linarith
  exact hne (norm_le_zero_iff.1 this)

end PositivityTheory.Rg.Sw.LVs
