import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeFirstStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapStarMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.CoefFilt

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def wInt (f : ℝ → ℂ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))

theorem wInt_anti {s s' : ℝ} (h : s ≤ s') (f : ℝ → ℂ) : wInt f s' ≤ wInt f s := by
  unfold wInt
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have : -2 * s' * t ≤ -2 * s * t := by nlinarith
  gcongr

theorem enorm_add_sq_le (a b : ℂ) : ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h : ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [norm_add_le a b, norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h

theorem measurable_integrand {f : ℝ → ℂ} (hf : Continuous f) (s : ℝ) :
    Measurable fun t : ℝ => ‖f t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t)) := by
  have h1 : Measurable fun t : ℝ => ‖f t‖ₑ := hf.measurable.enorm
  have h2 : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-2 * s * t)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  exact (h1.pow_const 2).mul h2

def weightedL2Continuous (s : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | Continuous f ∧ wInt f s < ⊤}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨hf.add hg, lt_of_le_of_lt (b := 2 * wInt f s + 2 * wInt g s) ?_ ?_⟩
    · unfold wInt
      rw [← lintegral_const_mul _ (measurable_integrand hf s), ← lintegral_const_mul _ (measurable_integrand hg s),
        ← lintegral_add_left ((measurable_integrand hf s).const_mul _)]
      refine lintegral_mono fun t => ?_
      calc ‖(f + g) t‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * s * t))
          ≤ (2 * ‖f t‖ₑ ^ 2 + 2 * ‖g t‖ₑ ^ 2) * ENNReal.ofReal (Real.exp (-2 * s * t)) := by
            gcongr
            exact enorm_add_sq_le _ _
        _ = _ := by ring
    · exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hf', ENNReal.mul_lt_top (by simp) hg'⟩
  zero_mem' := ⟨continuous_const, by simp [wInt]⟩
  smul_mem' := by
    rintro a f ⟨hf, hf'⟩
    refine ⟨hf.const_smul a, ?_⟩
    have : wInt (a • f) s = ‖a‖ₑ ^ 2 * wInt f s := by
      unfold wInt
      rw [← lintegral_const_mul _ (measurable_integrand hf s)]
      refine lintegral_congr fun t => ?_
      simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
      ring
    rw [this]
    exact ENNReal.mul_lt_top (by simp [ENNReal.pow_lt_top]) hf'

theorem inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (hh : Formalism.REAL.inUJ ε h) : Formalism.REAL.inUJ ε (g * h) := by
  unfold Formalism.REAL.inUJ at *
  calc (g * h)ᴴ * Formalism.REAL.Jm ε * (g * h) = hᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hg, hh]

section Fam

variable {ε : Fin n → Bool} {X : GMod n} {ι : Type} {c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
  {A : Matrix (Fin n) (Fin n) ℂ}

def line (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (A g : Matrix (Fin n) (Fin n) ℂ) (i : ι) (u : X.V) :
    ℝ → ℂ := fun t => c i u (g * NormedSpace.exp ((t : ℂ) • A))

theorem line_hasDerivAt (hc : IsCoefFam ε X c) (hA : Formalism.REAL.inG ε A) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) (i : ι) (u : X.V) (t : ℝ) :
    HasDerivAt (line c A g i u) (line c A g i (actM X.E A u) t) t := by
  have h := hc.1 i u A hA (g * NormedSpace.exp ((t : ℂ) • A)) (inUJ_mul hg (Formalism.REAL.exp_indefinite_unitary_holds n ε A hA t))
  have h' : HasDerivAt (fun t' : ℝ => c i u (g * NormedSpace.exp ((t : ℂ) • A) *
      NormedSpace.exp (((t' - t : ℝ) : ℂ) • A))) (c i (actM X.E A u) (g * NormedSpace.exp ((t : ℂ) • A))) t :=
    HasDerivAt.comp_sub_const t t (by simpa using h)
  refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  have e := exp_add_smul A t (r - t)
  simp only [line]
  rw [Matrix.mul_assoc, ← e]
  simp

theorem line_continuous (hc : IsCoefFam ε X c) (hA : Formalism.REAL.inG ε A) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) (i : ι) (u : X.V) : Continuous (line c A g i u) :=
  continuous_iff_continuousAt.2 fun t => (line_hasDerivAt hc hA hg i u t).continuousAt

theorem mem_NSet_iff (hc : IsCoefFam ε X c) (hA : Formalism.REAL.inG ε A) (μ : Measure (S7.UJ ε)) (s : ℝ) (u : X.V) :
    u ∈ NSet ε c A μ s ↔ ∀ i, ∀ᵐ x ∂μ, line c A (S7.toM x) i u ∈ weightedL2Continuous s := by
  refine forall_congr' fun i => Filter.eventually_congr (Filter.Eventually.of_forall fun x => ?_)
  exact ⟨fun h => ⟨line_continuous hc hA x.2 i u, h⟩, fun h => h.2⟩

def Nsub (hc : IsCoefFam ε X c) (hA : Formalism.REAL.inG ε A) (μ : Measure (S7.UJ ε)) (s : ℝ) : Submodule ℂ X.V where
  carrier := NSet ε c A μ s
  add_mem' := by
    intro u v hu hv
    have hu' := (mem_NSet_iff hc hA μ s u).1 hu
    have hv' := (mem_NSet_iff hc hA μ s v).1 hv
    refine (mem_NSet_iff hc hA μ s (u + v)).2 fun i => ?_
    filter_upwards [hu' i, hv' i] with x h1 h2
    have e : line c A (S7.toM x) i (u + v) = line c A (S7.toM x) i u + line c A (S7.toM x) i v := by
      funext t
      simp [line]
    rw [e]
    exact (weightedL2Continuous s).add_mem h1 h2
  zero_mem' := by
    refine (mem_NSet_iff hc hA μ s 0).2 fun i => Filter.Eventually.of_forall fun x => ?_
    have e : line c A (S7.toM x) i 0 = 0 := by
      funext t
      simp [line]
    rw [e]
    exact (weightedL2Continuous s).zero_mem
  smul_mem' := by
    intro a u hu
    have hu' := (mem_NSet_iff hc hA μ s u).1 hu
    refine (mem_NSet_iff hc hA μ s (a • u)).2 fun i => ?_
    filter_upwards [hu' i] with x h1
    have e : line c A (S7.toM x) i (a • u) = a • line c A (S7.toM x) i u := by
      funext t
      simp [line]
    rw [e]
    exact (weightedL2Continuous s).smul_mem a h1

theorem exp_conj_eq {A Y : Matrix (Fin n) (Fin n) ℂ} {k : ℤ} (hY : A * Y - Y * A = (k : ℂ) • Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) * Y = ((Real.exp (k * t) : ℝ) : ℂ) • (Y * NormedSpace.exp ((t : ℂ) • A)) := by
  have h0 : A * Y = Y * A + (k : ℂ) • Y := by rw [← hY]; abel
  have h1 : ((t : ℂ) • A) * Y = Y * ((t : ℂ) • A + ((k * t : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [Matrix.smul_mul, h0, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul,
      mul_comm (t : ℂ)]
  have h2 : NormedSpace.exp (((k * t : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      ((Real.exp (k * t) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    push_cast
    rfl
  rw [GlobalTheory.IndLine.Iwasawa.exp_mul_eq h1,
    Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _), h2]
  simp

theorem left_expand {i : ι} {l : Fin n → Fin n → ι →₀ ℂ}
    (hl : ∀ (a b : Fin n) (u : X.V) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      c i (X.E a b u) g = ∑ c', ∑ d, (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c' d *
        (l c' d).sum fun i' r => r * c i' u g)
    (Y : Matrix (Fin n) (Fin n) ℂ) (u : X.V) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    c i (actM X.E Y u) g = ∑ c', ∑ d, (g * Y * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c' d *
      (l c' d).sum fun i' r => r * c i' u g := by
  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    ∑ c', ∑ d, ((l c' d).sum fun i' r => r * c i' u g) • Matrix.entryLinearMap ℂ ℂ c' d
  have hΦ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Φ M = ∑ c', ∑ d, M c' d * (l c' d).sum fun i' r => r * c i' u g := by
    intro M
    simp only [Φ, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.entryLinearMap_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hY : g * Y * g⁻¹ = ∑ a, ∑ b, Y a b • (g * Matrix.single a b (1 : ℂ) * g⁻¹) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) by simp [Matrix.smul_single],
      Matrix.mul_smul, Matrix.smul_mul]
  have hL : c i (actM X.E Y u) g = ∑ a, ∑ b, Y a b * Φ (g * Matrix.single a b (1 : ℂ) * g⁻¹) := by
    simp only [hΦ, ← hl _ _ u g hg, actM, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hL, ← hΦ, hY]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem wInt_shift {f h : ℝ → ℂ} {k s : ℝ} (hp : ∀ t, f t = ((Real.exp (k * t) : ℝ) : ℂ) * h t) :
    wInt f (s + k) = wInt h s := by
  unfold wInt
  refine lintegral_congr fun t => ?_
  have e : ‖((Real.exp (k * t) : ℝ) : ℂ)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-2 * (s + k) * t)) =
      ENNReal.ofReal (Real.exp (-2 * s * t)) := by
    have e1 : ‖((Real.exp (k * t) : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.exp (k * t)) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [e1, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity), sq, ← Real.exp_add,
      ← Real.exp_add]
    congr 2
    ring
  rw [hp t, enorm_mul, mul_pow, mul_comm (_ ^ 2) (_ ^ 2), mul_assoc, e]

theorem shift_mem (hc : IsCoefFam ε X c) (hA : Formalism.REAL.inG ε A) (μ : Measure (S7.UJ ε))
    (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℤ) (hY : A * Y - Y * A = (k : ℂ) • Y) (s : ℝ) (u : X.V)
    (hu : u ∈ NSet ε c A μ s) : actM X.E Y u ∈ NSet ε c A μ (s + k) := by
  have hu' := (mem_NSet_iff hc hA μ s u).1 hu
  refine (mem_NSet_iff hc hA μ (s + k) _).2 fun i => ?_
  obtain ⟨l, hl⟩ := hc.2 i
  have hall : ∀ᵐ x ∂μ, ∀ c' d, ∀ i' ∈ (l c' d).support, line c A (S7.toM x) i' u ∈ weightedL2Continuous s := by
    rw [ae_all_iff]
    intro c'
    rw [ae_all_iff]
    intro d
    exact (Filter.eventually_all_finset _).2 fun i' _ => hu' i'
  filter_upwards [hall] with x hx
  let K : Matrix (Fin n) (Fin n) ℂ := S7.toM x * Y * (S7.toM x)⁻¹
  let h : ℝ → ℂ := ∑ c', ∑ d, K c' d • ∑ i' ∈ (l c' d).support, (l c' d i') • line c A (S7.toM x) i' u
  have hh : h ∈ weightedL2Continuous s := Submodule.sum_mem _ fun c' _ => Submodule.sum_mem _ fun d _ =>
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i' hi => Submodule.smul_mem _ _ (hx c' d i' hi))
  have hpt : ∀ t, line c A (S7.toM x) i (actM X.E Y u) t = ((Real.exp (k * t) : ℝ) : ℂ) * h t := by
    intro t
    have hE : NormedSpace.exp ((t : ℂ) • A) * (NormedSpace.exp ((t : ℂ) • A))⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
    have hconj : (S7.toM x * NormedSpace.exp ((t : ℂ) • A)) * Y * (S7.toM x * NormedSpace.exp ((t : ℂ) • A))⁻¹ =
        ((Real.exp (k * t) : ℝ) : ℂ) • K := by
      rw [Matrix.mul_inv_rev, Matrix.mul_assoc (S7.toM x), exp_conj_eq hY t]
      simp only [K, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc S7.toM x * (Y * NormedSpace.exp ((t : ℂ) • A)) * ((NormedSpace.exp ((t : ℂ) • A))⁻¹ * (S7.toM x)⁻¹)
          = S7.toM x * Y * (NormedSpace.exp ((t : ℂ) • A) * (NormedSpace.exp ((t : ℂ) • A))⁻¹) * (S7.toM x)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hE, Matrix.mul_one]
    have hgU : Formalism.REAL.inUJ ε (S7.toM x * NormedSpace.exp ((t : ℂ) • A)) :=
      inUJ_mul x.2 (Formalism.REAL.exp_indefinite_unitary_holds n ε A hA t)
    change c i (actM X.E Y u) (S7.toM x * NormedSpace.exp ((t : ℂ) • A)) = _
    rw [left_expand hl Y u hgU, hconj]
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Finset.mul_sum, Finsupp.sum, line]
    refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun i' _ => ?_
    ring
  exact ⟨line_continuous hc hA x.2 i _, by
    have := wInt_shift (s := s) (k := (k : ℝ)) hpt
    rw [this]
    exact hh.2⟩

theorem eig_bounds (hc : IsCoefFam ε X c) (hA : Formalism.REAL.inG ε A) (μ : Measure (S7.UJ ε)) {s s' : ℝ}
    (hlt : s' < s) (htop : ∀ u, u ∈ NSet ε c A μ s) (z : ℂ) (u : X.V) (hu : u ∉ NSet ε c A μ s')
    (hv : actM X.E A u - z • u ∈ NSet ε c A μ s') : s' ≤ z.re ∧ z.re < s := by
  rw [mem_NSet_iff hc hA μ s' u] at hu
  obtain ⟨i, hi⟩ := not_forall.1 hu
  have hv' := (mem_NSet_iff hc hA μ s' _).1 hv i
  have ht := (mem_NSet_iff hc hA μ s u).1 (htop u) i
  have ode : ∀ (x : S7.UJ ε) (t : ℝ), HasDerivAt (line c A (S7.toM x) i u)
      (z * line c A (S7.toM x) i u t + line c A (S7.toM x) i (actM X.E A u - z • u) t) t := by
    intro x t
    have h := line_hasDerivAt hc hA x.2 i u t
    convert h using 1
    simp [line]
  constructor
  · by_contra hz
    refine hi ?_
    filter_upwards [hv'] with x hg
    exact ⟨line_continuous hc hA x.2 i u,
      GlobalTheory.T.NilpotentOdeFirst z s' (not_le.1 hz) _ _ (fun t _ => ode x t) hg.1 hg.2⟩
  · by_contra hz
    have hz' : s ≤ z.re := not_lt.1 hz
    refine hi ?_
    filter_upwards [hv', ht] with x hg hf
    exact ⟨line_continuous hc hA x.2 i u,
      GlobalTheory.T.NilpotentOdeSecond z s' s (lt_of_lt_of_le hlt hz') hz' _ _ (fun t _ => ode x t) hg.1 hg.2 hf.2⟩

end Fam

theorem famFilt : CompanionTheory.RgExh.Dec.J.FamFilt := by
  intro n ε X ι c A μ hc hA _ hs
  obtain ⟨s0, h0⟩ := hs
  have hG : Formalism.REAL.inG ε A := hA.1
  refine ⟨⟨Nsub hc hG μ, ?_, ?_, ?_, ?_⟩, fun s u => Iff.rfl⟩
  · intro s s' hss u hu i
    filter_upwards [hu i] with x h
    exact lt_of_le_of_lt (wInt_anti hss _) h
  · exact ⟨s0, eq_top_iff.2 fun u _ => h0 u⟩
  · intro Y k hY s u hu
    exact shift_mem hc hG μ Y k hY s u hu
  · intro s s' hlt htop z u hu hv
    exact eig_bounds hc hG μ hlt (fun v => by
      have : v ∈ Nsub hc hG μ s := by rw [htop]; trivial
      exact this) z u hu hv

end GlobalTheory.CompanionTheory.CoefFilt
