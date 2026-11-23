import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatCons
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

private theorem taylor2 {f f' f'' : ℝ → ℂ} (h1 : ∀ v, HasDerivAt f (f' v) v) (h2 : ∀ v, HasDerivAt f' (f'' v) v) {t K : ℝ}
    (hK : ∀ v ∈ Metric.closedBall t 1, ‖f'' v‖ ≤ K) {x : ℝ} (hx : |x| ≤ 1) : ‖f (t + x) - f t - x * f' t‖ ≤ K * x ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK t (Metric.mem_closedBall_self zero_le_one))
  have a : ∀ v ∈ Metric.closedBall t |x|, ‖f' v - f' t‖ ≤ K * |x| := fun v hv =>
    ((convex_closedBall t 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun y _ => (h2 y).hasDerivWithinAt) hK
      (Metric.mem_closedBall_self zero_le_one) (Metric.closedBall_subset_closedBall hx hv)).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.1 hv) hK0)
  have b := (convex_closedBall t |x|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun v : ℝ => f v - v * f' t)
    (f' := fun v => f' v - f' t) (fun y _ => by
      have := ((h1 y).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const (f' t))).hasDerivWithinAt
        (s := Metric.closedBall t |x|)
      simpa using this) a
    (Metric.mem_closedBall_self (abs_nonneg x)) (y := t + x) (by simp)
  have e : f (t + x) - ((t + x : ℝ) : ℂ) * f' t - (f t - t * f' t) = f (t + x) - f t - x * f' t := by push_cast; ring
  rw [e, add_sub_cancel_left, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, ← sq] at b
  exact b

private theorem comp_sub (d : Dat S n) {φ ψ χ : Sm E n} (c : ℂ) (h1 : Umg φ) (h2 : Umg ψ) (h3 : Umg χ) (t : Fin d.len → ℝ) :
    d.comp (φ - ψ - c • χ).1 t = d.comp φ.1 t - d.comp ψ.1 t - c * d.comp χ.1 t := by
  have e : φ - ψ - c • χ = (-c) • χ + ((-1 : ℂ) • ψ + φ) := by module
  rw [e, (compBound E S n d).2 _ _ _ h3 ((h2.smul _).add h1), (compBound E S n d).2 _ _ _ h2 h1]
  ring

private theorem deriv0 (b : Blo S r) (d : Dat S s) {φ : Sm E (r + s)} (hφ : Umg φ) (t₀ : ℝ) (t : Fin d.len → ℝ) :
    HasDerivAt (fun x : ℝ => d.comp (slice b.f.1 (t₀ + x) φ.1) t) (d.comp (slice b.f.1 t₀ (j1 E r s φ).1) t) 0 := by
  obtain ⟨N, B, hB⟩ := hφ.j1.j1.bound
  obtain ⟨C, R, hC⟩ := (sliceBound E S r s b).1 N
  obtain ⟨C', R', hC'⟩ := (compBound E S s d).1 N
  choose ψ hψ hu _ using fun v => sliceUmg E S r s b v φ hφ
  obtain ⟨χ, hχ, hu', -⟩ := sliceUmg E S r s b t₀ _ hφ.j1
  set K := |C * B| * Real.exp (|R| * (|t₀| + 1))
  have key : ∀ x : ℝ, |x| ≤ 1 → ∀ m, ‖(ψ (t₀ + x) - ψ t₀ - (x : ℂ) • χ).1 m‖ ≤ K * x ^ 2 * AutomorphicForm.height m ^ N := by
    intro x hx m
    have hm : 0 ≤ AutomorphicForm.height m ^ N := (pow_pos (AutomorphicForm.height_pos m) N).le
    have := taylor2 (fun v => (sliceShift E S r s b v φ m hφ).2) (fun v => (sliceShift E S r s b v _ m hφ.j1).2)
      (t := t₀) (K := K * AutomorphicForm.height m ^ N) (fun v hv => by
        refine (hC _ B hφ.j1.j1 hB v m).trans (mul_le_mul_of_nonneg_right ?_ hm)
        have hv' : |v| ≤ |t₀| + 1 := by
          have := abs_sub_abs_le_abs_sub v t₀
          have : |v - t₀| ≤ 1 := hv
          linarith
        exact mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 (mul_le_mul (le_abs_self R) hv' (abs_nonneg _) (abs_nonneg _)))
          (Real.exp_pos _).le (abs_nonneg _)) hx
    rw [← hψ, ← hψ, ← hχ, mul_right_comm] at this
    exact this
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun x : ℝ => x ^ 2)
    (Asymptotics.IsBigO.of_bound (C' * K * Real.exp (R' * ‖t‖)) ?_) (Asymptotics.isLittleO_pow_id one_lt_two)
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with x hx
  have h := hC' _ _ (((hu (t₀ + x)).sub (hu t₀)).sub (hu'.smul x)) (key x (by simpa using hx)) t
  rw [comp_sub d _ (hu _) (hu _) hu', hψ, hψ, hχ] at h
  rw [zero_add, add_zero, Complex.real_smul, Real.norm_of_nonneg (sq_nonneg x)]
  exact h.trans (le_of_eq (by ring))

private theorem main : ∀ {n : ℕ} (d : Dat S n) (φ : Sm E n) (t : Fin d.len → ℝ), Umg φ →
    (∀ v, d.comp (rt E n (d.tr v) φ).1 t = d.comp φ.1 (t + v)) ∧
    ∀ j, HasDerivAt (fun x : ℝ => d.comp φ.1 (t + Pi.single j x)) (d.comp (d.J j φ).1 t) 0 := by
  intro n d
  induction d with
  | nil => exact fun φ t _ => ⟨fun v => congrArg φ.1 (Subsingleton.elim _ _), fun j => j.elim0⟩
  | @cons r s b d ih =>
    intro φ t hφ
    refine ⟨fun v => ?_, Dat.sc_cases b d ?_ fun j => ?_⟩
    · obtain ⟨ψ, e, hψ, -⟩ := sliceUmg E S r s b (t (Dat.z0 b d) + v (Dat.z0 b d)) φ hφ
      have h := Lnk.tr (d.tr fun j => v (Dat.sc b d j)) _ φ ψ hφ e
      have e1 : (Dat.cons b d).tr v = lev (Ad E) r s (zt E r (v (Dat.z0 b d)), 1) *
          lev (Ad E) r s (1, d.tr fun j => v (Dat.sc b d j)) := by
        rw [Dat.tr_cons, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
      have e2 := funext fun m => (sliceShift E S r s b (t (Dat.z0 b d)) _ m h.1).1 (v (Dat.z0 b d))
      rw [Dat.comp_cons, Dat.comp_cons, e1, map_mul, Module.End.mul_apply,
        show slice _ _ _ = _ from e2.trans h.2.symm, (ih ψ _ hψ).1, e]
      rfl
    · have h := deriv0 b d hφ (t (Dat.z0 b d)) fun j => t (Dat.sc b d j)
      rw [Dat.J_zero, Dat.comp_cons]
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
      simp only [Dat.comp_cons, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Dat.sc_ne b d _), add_zero]
    · obtain ⟨ψ, e, hψ, -⟩ := sliceUmg E S r s b (t (Dat.z0 b d)) φ hφ
      have h := (ih ψ (fun j => t (Dat.sc b d j)) hψ).2 j
      rw [(Lnk.J d j _ φ ψ hφ e).2, e] at h
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
      simp only [Dat.comp_cons, Pi.add_apply, Pi.single_eq_of_ne (Dat.sc_ne b d _).symm, add_zero]
      congr 1
      funext l
      simp only [Pi.add_apply, Pi.single_apply, Dat.sc_inj]

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.compShift :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CompShift E :=
  fun _ _ _ _ _ _ d => UpperTheory.ConvolutionTheory.BW.main d
