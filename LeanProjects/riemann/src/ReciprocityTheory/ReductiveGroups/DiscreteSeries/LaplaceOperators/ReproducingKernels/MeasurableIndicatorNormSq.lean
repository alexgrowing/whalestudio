import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fwd

open Formalism.QuantumDeterminants

theorem norm_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (m : Mat k r) :
    ‖Formalism.MainNotions.S.psiGen k r z c m‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem UH_mul_iff {n : ℕ} (H s x : Matrix (Fin n) (Fin n) ℂ) (hs : s ∈ UH H) :
    s * x ∈ UH H ↔ x ∈ UH H := by
  have hs' : sᴴ * H * s = H := hs
  have key : (s * x)ᴴ * H * (s * x) = xᴴ * H * x := by
    rw [conjTranspose_mul]
    calc xᴴ * sᴴ * H * (s * x) = xᴴ * (sᴴ * H * s) * x := by simp only [Matrix.mul_assoc]
      _ = xᴴ * H * x := by rw [hs']
  show (s * x)ᴴ * H * (s * x) = H ↔ xᴴ * H * x = H
  rw [key]

theorem Sset_mul_mem_iff (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r)
    (hs : s ∈ Sset k r z) : s * x ∈ UH (Hpk k r) ↔ x ∈ UH (Hpk k r) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hsU : h * m ∈ UH (Hpk k r) := (UH_mul_iff _ h m hh.1).2 hm.1
  exact UH_mul_iff _ _ x hsU

theorem isClosed_setUH (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  have hc : Continuous (fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y) := by
    have h1 : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
    exact ((h1.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h1
  exact isClosed_eq hc continuous_const

theorem measurable_indicator_normSq (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp]
    (W : Mat k r → Vp)
    (hW : ContinuousOn (fun y : Mt k r => W (Matrix.of y)) {y | Matrix.of y ∈ UH (Hpk k r)}) :
    Measurable (Set.indicator {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}
      (fun y => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2)) := by
  classical
  have hC := isClosed_setUH k r
  have hf : ContinuousOn (fun y : Mt k r => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2)
      {y | Matrix.of y ∈ UH (Hpk k r)} :=
    (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hW)
  have := hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞))) hC.measurableSet
  rw [← Set.piecewise_eq_indicator]
  exact this

theorem lintegral_pos (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] (μG : Measure (Mt k r))
    (W : Mat k r → Vp) (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG)
    (hopen : ∀ U : Set (Mt k r), IsOpen U → (∃ y ∈ U, Matrix.of y ∈ UH (Hpk k r)) → 0 < μG U)
    (hW : ContinuousOn (fun y : Mt k r => W (Matrix.of y)) {y | Matrix.of y ∈ UH (Hpk k r)})
    (hne : ∃ y ∈ UH (Hpk k r), W y ≠ 0) :
    0 < ∫⁻ y, Set.indicator {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}
      (fun y => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2) y ∂μG := by
  obtain ⟨y0, hy0, hWy0⟩ := hne
  rw [lintegral_pos_iff_support (measurable_indicator_normSq k r Vp W hW)]
  have hy0' : (y0 : Mt k r) ∈ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hy0
  have hnh : (fun y : Mt k r => W (Matrix.of y)) ⁻¹' {v | v ≠ 0} ∈
      nhdsWithin (y0 : Mt k r) {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} :=
    (hW _ hy0').preimage_mem_nhdsWithin (isOpen_ne.mem_nhds hWy0)
  obtain ⟨U, hUo, hyU, hUsub⟩ := mem_nhdsWithin.1 hnh
  have hpos : 0 < μG U := hopen U hUo ⟨y0, hyU, hy0⟩
  refine lt_of_lt_of_le hpos (measure_mono_ae ?_)
  have hae : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by
    rw [ae_iff]; simpa using hG.2.2.1
  filter_upwards [hae] with y hy hyU'
  have hyW : W (Matrix.of y) ≠ 0 := hUsub ⟨hyU', hy⟩
  show Set.indicator _ _ y ≠ 0
  rw [Set.indicator_of_mem (show y ∈ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} from hy)]
  simpa using hyW

theorem nonzero : NonzeroStatement := by
  intro k r z c Vp _ _ π μG μS ν W hπ hG hS hQ hopen hW hEq hne h0
  set g : Mt k r → ℝ≥0∞ := Set.indicator {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}
      (fun y => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2) with hgdef
  have hgm : Measurable g := measurable_indicator_normSq k r Vp W hW
  have hpos : 0 < ∫⁻ y, g y ∂μG := lintegral_pos k r Vp μG W hG hopen hW hne
  have hQg := hQ g hgm
  have hSae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS.2.2.1
  have hin : ∀ x : Mt k r,
      ∫⁻ s, g (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤ ∫⁻ _s, g x ∂μS := by
    intro x
    refine lintegral_mono_ae ?_
    filter_upwards [hSae] with s hs
    by_cases hx : Matrix.of x ∈ UH (Hpk k r)
    · have hsx : Matrix.of s * Matrix.of x ∈ UH (Hpk k r) :=
        (Sset_mul_mem_iff k r z _ _ hs).2 hx
      obtain ⟨h, hh, m, hm, hsd⟩ := hs
      have hm1 : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈
          {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hsx
      have hm2 : x ∈ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hx
      rw [hgdef, Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
      have heq : W (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j)) =
          Formalism.MainNotions.S.psiGen k r z c m • π h (W (Matrix.of x)) := by
        show W (Matrix.of s * Matrix.of x) = _
        rw [hsd]
        exact hEq h hh m hm _ hx
      have hn : ‖Formalism.MainNotions.S.psiGen k r z c m • π h (W (Matrix.of x))‖₊ = ‖W (Matrix.of x)‖₊ :=
        NNReal.eq (by rw [coe_nnnorm, coe_nnnorm, norm_smul, norm_psiGen, one_mul, hπ h hh])
      rw [heq, hn]
    · have hm2 : x ∉ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hx
      have hsx : Matrix.of s * Matrix.of x ∉ UH (Hpk k r) :=
        fun hh => hx ((Sset_mul_mem_iff k r z _ _ hs).1 hh)
      have hm1 : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∉
          {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hsx
      rw [hgdef, Set.indicator_of_notMem hm1]
      exact zero_le
  have hle : ∫⁻ y, g y ∂μG ≤ 0 := by
    rw [hQg]
    calc ∫⁻ x, (∫⁻ s, g (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν
        ≤ ∫⁻ x, g x * μS Set.univ ∂ν := by
          refine lintegral_mono fun x => ?_
          refine (hin x).trans ?_
          rw [lintegral_const]
      _ = (∫⁻ x, g x ∂ν) * μS Set.univ := lintegral_mul_const _ hgm
      _ ≤ (∫⁻ x, (‖W (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν) * μS Set.univ := by
          gcongr with x
          exact Set.indicator_le_self _ _ x
      _ = 0 := by
          have : Formalism.MainNotions.S.l2SG ν W = ∫⁻ x, (‖W (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := rfl
          rw [← this, h0, zero_mul]
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fwd
