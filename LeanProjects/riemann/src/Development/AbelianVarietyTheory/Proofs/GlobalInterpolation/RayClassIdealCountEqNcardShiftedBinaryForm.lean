import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlaneLatticeShortBasisOfBoundPowTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersSqrtNegThreeModFour

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayForm

open GlobalTheory.Mem.PartialZeta

theorem exists_qForm (f₁ f₂ x₀ : ℂ) (N : ℝ) (hN : N ≠ 0) (hA : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0) :
    ∃ l θ₁ θ₂ : ℝ, ∀ v : ℤ × ℤ,
      qForm (‖f₁‖ ^ 2 / N) (((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * N)) l θ₁ θ₂ v =
        ‖x₀ + (v.1 * f₁ + v.2 * f₂)‖ ^ 2 / N := by
  have hf : f₁ ≠ 0 := by
    rintro rfl
    simp at hA
  have e1 : ((starRingEnd ℂ) f₁ * f₂).re = f₁.re * f₂.re + f₁.im * f₂.im := by
    simp [Complex.mul_re]
  have e2 : ((starRingEnd ℂ) f₁ * f₂).im = f₁.re * f₂.im - f₁.im * f₂.re := by
    simp [Complex.mul_im]
    ring
  have e3 : ((starRingEnd ℂ) f₁ * x₀).re = f₁.re * x₀.re + f₁.im * x₀.im := by
    simp [Complex.mul_re]
  have e4 : ((starRingEnd ℂ) f₁ * x₀).im = f₁.re * x₀.im - f₁.im * x₀.re := by
    simp [Complex.mul_im]
    ring
  have e5 : ‖f₁‖ ^ 2 = f₁.re ^ 2 + f₁.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hS : f₁.re ^ 2 + f₁.im ^ 2 ≠ 0 := by
    rw [← e5]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hf)
  refine ⟨((starRingEnd ℂ) f₁ * f₂).re / ‖f₁‖ ^ 2, ((starRingEnd ℂ) f₁ * x₀).re / ‖f₁‖ ^ 2,
    ((starRingEnd ℂ) f₁ * x₀).im / ((starRingEnd ℂ) f₁ * f₂).im, fun v => ?_⟩
  have e6 : ‖x₀ + ((v.1 : ℂ) * f₁ + (v.2 : ℂ) * f₂)‖ ^ 2 =
      (x₀.re + v.1 * f₁.re + v.2 * f₂.re) ^ 2 + (x₀.im + v.1 * f₁.im + v.2 * f₂.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [e2] at hA
  simp only [qForm]
  rw [e6, e1, e2, e3, e4, e5]
  field_simp
  ring

theorem comb_injective (f₁ f₂ : ℂ) (hA : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0) :
    Function.Injective (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) := by
  have hf : f₁ ≠ 0 := by
    rintro rfl
    simp at hA
  have key : ∀ x y : ℤ, (x : ℂ) * f₁ + y * f₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have him : ((starRingEnd ℂ) f₁ * ((x : ℂ) * f₁ + y * f₂)).im =
        y * ((starRingEnd ℂ) f₁ * f₂).im := by
      simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
      ring
    rw [h, mul_zero, Complex.zero_im] at him
    have hy : y = 0 := by
      have : (y : ℝ) = 0 := by
        rcases mul_eq_zero.mp him.symm with h' | h'
        · exact h'
        · exact absurd h' hA
      exact_mod_cast this
    subst hy
    refine ⟨?_, rfl⟩
    simp only [Int.cast_zero, zero_mul, add_zero, mul_eq_zero, hf, or_false] at h
    exact_mod_cast h
  intro v w hvw
  have := key (v.1 - w.1) (v.2 - w.2) (by push_cast; linear_combination hvw)
  exact Prod.ext (sub_eq_zero.mp this.1) (sub_eq_zero.mp this.2)

theorem range_comb (f₁ f₂ : ℂ) :
    Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) = (Submodule.span ℤ {f₁, f₂} : Submodule ℤ ℂ) := by
  ext z
  simp only [Set.mem_range, SetLike.mem_coe, Submodule.mem_span_pair, zsmul_eq_mul, Prod.exists]

theorem exists_equiv (f₁ f₂ e₁ e₂ : ℂ) (hf : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0)
    (he : ((starRingEnd ℂ) e₁ * e₂).im ≠ 0)
    (h : Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂}) :
    ∃ σ : ℤ × ℤ ≃ ℤ × ℤ, ∀ v, (v.1 : ℂ) * f₁ + v.2 * f₂ = (σ v).1 * e₁ + (σ v).2 * e₂ := by
  have hr : Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) =
      Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * e₁ + v.2 * e₂) := by
    rw [range_comb, range_comb, h]
  refine ⟨(Equiv.ofInjective _ (comb_injective f₁ f₂ hf)).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective _ (comb_injective e₁ e₂ he)).symm), fun v => ?_⟩
  have key := Equiv.apply_ofInjective_symm (comb_injective e₁ e₂ he)
    (Equiv.setCongr hr (Equiv.ofInjective _ (comb_injective f₁ f₂ hf) v))
  simp only [Equiv.setCongr_apply, Equiv.ofInjective_apply] at key
  simp only [Equiv.trans_apply, Equiv.setCongr_apply, Equiv.ofInjective_apply]
  exact key.symm

variable {K : Type} [Field K] [NumberField K]

theorem unit_eq_one [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) {M : ℕ} (hM : 3 ≤ M)
    (u : (𝓞 K)ˣ) (hu : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}) : u = 1 := by
  let φ : K →+* ℂ := (Classical.arbitrary (InfinitePlace K)).embedding
  by_contra hne
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hu
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hne (Units.val_eq_one.mp (by linear_combination -ht))
  have hu1 : ‖φ ((u : 𝓞 K) : K)‖ ^ 2 = 1 := by
    rw [normSq_eq h2 φ (u : 𝓞 K), Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top]
    simp
  have ht1 : 1 ≤ ‖φ ((t : 𝓞 K) : K)‖ ^ 2 := by
    rw [normSq_eq h2 φ t]
    have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have he : φ ((u : 𝓞 K) : K) - 1 = φ ((t : 𝓞 K) : K) * M := by
    have := congrArg (fun z : 𝓞 K => φ (z : K)) ht
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    simp only [RingOfIntegers.coe_eq_algebraMap]
    rw [← this]
  have hle : ‖φ ((t : 𝓞 K) : K)‖ * M ≤ 2 := by
    have h1 : ‖φ ((u : 𝓞 K) : K)‖ = 1 := by
      have := norm_nonneg (φ ((u : 𝓞 K) : K))
      nlinarith
    calc ‖φ ((t : 𝓞 K) : K)‖ * M = ‖φ ((u : 𝓞 K) : K) - 1‖ := by
          rw [he, norm_mul, Complex.norm_natCast]
      _ ≤ ‖φ ((u : 𝓞 K) : K)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, norm_one]; norm_num
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hn := norm_nonneg (φ ((t : 𝓞 K) : K))
  nlinarith

theorem exists_basis_im {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3) {x : K} (hx : x ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) :
    ∃ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ^ 2 = d / 4 := by
  obtain ⟨w, hw, hall⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 (Irreducible.squarefree hp) hd hx
  have hφx : φ x ^ 2 = -(d : ℂ) := by rw [← map_pow, hx]; simp
  have hφw : φ (w : K) = (1 + φ x) / 2 := by
    have := congrArg φ hw
    simp only [map_mul, map_add, map_one, map_ofNat] at this
    linear_combination this / 2
  have hsd : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have him : (φ (w : K)).im = √(d : ℝ) / 2 ∨ (φ (w : K)).im = -(√(d : ℝ) / 2) := by
    rcases GlobalTheory.eq_I_mul_sqrt_or_of_sq_eq_neg hφx with h | h
    · left
      rw [hφw, h]
      simp
    · right
      rw [hφw, h]
      simp
      ring
  have himne : (φ (w : K)).im ≠ 0 := by
    rcases him with h | h <;> rw [h] <;> [exact (by positivity); exact neg_ne_zero.mpr (by positivity)]
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : t = 0 ∨ (φ (w : K)).im = 0 := by
      have := congrArg (fun z : 𝓞 K => (φ (z : K)).im) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := h1.resolve_right himne
    subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro c _
    obtain ⟨m, n, hc⟩ := hall c
    have h1 : (1 : 𝓞 K) ∈ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) :=
      Submodule.subset_span ⟨0, rfl⟩
    have h2' : w ∈ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) :=
      Submodule.subset_span ⟨1, rfl⟩
    have := Submodule.add_mem _ (Submodule.smul_mem _ m h1) (Submodule.smul_mem _ n h2')
    rw [hc]
    simpa [zsmul_eq_mul] using this
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  have hbw : ((starRingEnd ℂ) (φ (((Module.Basis.mk hli hsp) 0 : 𝓞 K) : K)) *
      φ (((Module.Basis.mk hli hsp) 1 : 𝓞 K) : K)).im = (φ (w : K)).im := by
    simp [Module.Basis.mk_apply]
  rw [hbw]
  have hsq : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  rcases him with h | h <;> rw [h] <;> [skip; rw [neg_sq]] <;> rw [div_pow, hsq] <;> norm_num

theorem aRay_eq_ncard_qForm : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, ∃ α γ l θ₁ θ₂ : ℝ, 1 ≤ α ∧ 1 ≤ γ ∧ α * γ = d * (M : ℝ) ^ 4 / 4 ∧ (∀ v : ℤ × ℤ, ∃ n : ℕ, 1 ≤ n ∧ qForm α γ l θ₁ θ₂ v = n) ∧ ∀ n : ℕ, aRay D g n = (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v = n}.ncard : ℕ) : ℝ) := by
  intro K _ _ d M x hp hd hd100 hx h2 hM D g
  obtain ⟨w, bar, hw, hwb, hall, hemb, φ, hφ⟩ :=
    GlobalTheory.ringOfIntegers_sqrt_neg_three_mod_four d (Irreducible.squarefree hp) hd K h2 x hx
  have : IsTotallyComplex K :=
    ⟨fun v => InfinitePlace.isComplex_iff.mpr (hemb v.embedding).1⟩
  obtain ⟨b, hb⟩ := exists_basis_im hp hd hx h2 φ
  have hNnorm : Ideal.absNorm (Ideal.span {(M : 𝓞 K)}) = M ^ 2 := by
    have := normSq_eq h2 φ (M : 𝓞 K)
    simp only [map_natCast, Complex.norm_natCast] at this
    exact_mod_cast this.symm
  have hM9 : 9 ≤ M ^ 2 := by nlinarith
  have hNtop : Ideal.span {(M : 𝓞 K)} ≠ ⊤ := by
    intro h
    rw [h, Ideal.absNorm_top] at hNnorm
    omega
  have hN0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hNnorm
    omega
  obtain ⟨B, hBc, hB0, hBg⟩ := D.cls_surj g⁻¹
  obtain ⟨E0', hE0'⟩ := gen_bij hNtop D g B hBc hB0 hBg
  haveI hU : Unique {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}} :=
    { default := ⟨1, by simp⟩
      uniq := fun u => Subtype.ext (unit_eq_one h2 hM u.1 u.2) }
  obtain ⟨x₀, hx₀B, hx₀N⟩ : ∃ x₀ ∈ B, x₀ - 1 ∈ Ideal.span {(M : 𝓞 K)} := by
    obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp hBc
    refine ⟨i, hi, ?_⟩
    rw [show i - 1 = -j by linear_combination hij]
    exact Submodule.neg_mem _ hj
  have hNB0 : Ideal.span {(M : 𝓞 K)} * B ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hN0, hB0⟩
  obtain ⟨E1, hE1⟩ := lattice_bij (Ideal.span {(M : 𝓞 K)}) B hBc
    (Ideal.selfBasis b _ hNB0) x₀ hx₀B hx₀N
  have hIm := abs_im_eq φ b _ (Ideal.selfBasis b _ hNB0)
  set e := Ideal.selfBasis b _ hNB0 with he_def
  set e₁ : ℂ := φ (((e 0 : 𝓞 K)) : K) with he₁
  set e₂ : ℂ := φ (((e 1 : 𝓞 K)) : K) with he₂
  have hBn0 : Ideal.absNorm B ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hB0
  set Nr : ℝ := (Ideal.absNorm B : ℝ) with hNr
  have hNrpos : 0 < Nr := by
    rw [hNr]
    exact_mod_cast Nat.pos_of_ne_zero hBn0
  have hsd10 : (10 : ℝ) ≤ √(d : ℝ) := by
    rw [show (10 : ℝ) = √(100 : ℝ) by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hd100)
  have hsq : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hImb : |((starRingEnd ℂ) (φ ((b 0 : 𝓞 K) : K)) * φ ((b 1 : 𝓞 K) : K)).im| = √(d : ℝ) / 2 := by
    rw [← Real.sqrt_sq_eq_abs, hb, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hIme : |((starRingEnd ℂ) e₁ * e₂).im| = (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by
    rw [hIm, map_mul, hNnorm, hImb, hNr]
    push_cast
    ring
  have hA : ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hIme
    have : 0 < (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by positivity
    linarith
  obtain ⟨f₁, f₂, hspan, hImf, hshort⟩ := GlobalTheory.plane_lattice_short_basis e₁ e₂ hA
  have hAf : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hImf
    exact hA (abs_eq_zero.mp hImf.symm)
  obtain ⟨σ, hσ⟩ := exists_equiv f₁ f₂ e₁ e₂ hAf hA hspan
  obtain ⟨l, θ₁, θ₂, hq⟩ := exists_qForm f₁ f₂ (φ (x₀ : K)) Nr hNrpos.ne' hAf
  set Iv : ℝ := |((starRingEnd ℂ) f₁ * f₂).im| with hIv
  have hIv' : Iv = (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by rw [hImf, hIme]
  have hIsq : ((starRingEnd ℂ) f₁ * f₂).im ^ 2 = Iv ^ 2 := (sq_abs _).symm
  have hf₁ : f₁ ≠ 0 := by
    rintro rfl
    simp at hAf
  have hlow : (M : ℝ) ^ 2 * Nr ≤ ‖f₁‖ ^ 2 := by
    have hmem : f₁ ∈ Submodule.span ℤ {e₁, e₂} := hspan ▸ Submodule.subset_span (by simp)
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp hmem
    set y : 𝓞 K := r * (e 0 : 𝓞 K) + s * (e 1 : 𝓞 K) with hy
    have hyf : φ (y : K) = f₁ := by
      rw [← hrs, hy, he₁, he₂]
      simp [zsmul_eq_mul]
    have hyB : y ∈ Ideal.span {(M : 𝓞 K)} * B := by
      rw [hy]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (e 0).2) (Ideal.mul_mem_left _ _ (e 1).2)
    have hy0 : y ≠ 0 := by
      rintro h0
      rw [h0] at hyf
      simp at hyf
      exact hf₁ hyf.symm
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hyB)
    have hne : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hy0
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    rw [map_mul, hNnorm] at hle
    rw [← hyf, normSq_eq h2 φ y, hNr]
    exact_mod_cast hle
  let E0 := (Equiv.prodUnique _ {u : (𝓞 K)ˣ // (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}}).symm.trans E0'
  let Φ := σ.trans (E1.trans E0.symm)
  have key : ∀ v, qForm (‖f₁‖ ^ 2 / Nr) (((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * Nr)) l θ₁ θ₂ v =
      (Ideal.absNorm (Φ v).1 : ℝ) := by
    intro v
    rw [hq v, hσ v]
    have hE : (E0 (Φ v) : 𝓞 K) = E1 (σ v) := by
      simp only [Φ, Equiv.trans_apply, Equiv.apply_symm_apply]
    have hspanv : Ideal.span {((E1 (σ v)) : 𝓞 K)} = (Φ v).1 * B := by
      rw [← hE]
      exact hE0' _
    have hval : φ (x₀ : K) + (((σ v).1 : ℂ) * e₁ + ((σ v).2 : ℂ) * e₂) =
        φ (((E1 (σ v) : 𝓞 K)) : K) := by
      rw [hE1, he₁, he₂]
      simp
      ring
    rw [hval, normSq_eq h2 φ, hspanv, map_mul, hNr]
    push_cast
    field_simp
  refine ⟨‖f₁‖ ^ 2 / Nr, ((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * Nr), l, θ₁, θ₂,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hNrpos, one_mul]
    have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hM2 hNrpos.le]
  · have hf2 : 0 < ‖f₁‖ ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity), hIsq, one_mul]
    have h1 : ‖f₁‖ ^ 2 ≤ 2 * Iv := by rw [hImf]; exact hshort
    have h2' : 2 * Nr ≤ Iv := by
      have hM2 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      have hk : (2 : ℝ) ≤ (M : ℝ) ^ 2 * (√(d : ℝ) / 2) := by nlinarith
      rw [hIv']
      calc 2 * Nr ≤ (M : ℝ) ^ 2 * (√(d : ℝ) / 2) * Nr := mul_le_mul_of_nonneg_right hk hNrpos.le
        _ = (M : ℝ) ^ 2 * Nr * (√(d : ℝ) / 2) := by ring
    have hIv0 : 0 ≤ Iv := abs_nonneg _
    nlinarith
  · have hf2 : ‖f₁‖ ^ 2 ≠ 0 := by positivity
    rw [hIsq, hIv']
    field_simp
    rw [hsq]
    ring
  · intro v
    refine ⟨Ideal.absNorm (Φ v).1, ?_, key v⟩
    apply Nat.one_le_iff_ne_zero.mpr
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_bot_of_coprime hNtop (Φ v).2.1
  · intro n
    have hset : idealsIn D g n = (Subtype.val ∘ Φ) ''
        {v : ℤ × ℤ | qForm (‖f₁‖ ^ 2 / Nr) (((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * Nr))
          l θ₁ θ₂ v = n} := by
      ext I
      simp only [idealsIn, Set.mem_setOf_eq, Set.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨_, hIc, hIn, hIg⟩
        refine ⟨Φ.symm ⟨I, hIc, hIg⟩, ?_, by simp⟩
        rw [key, Equiv.apply_symm_apply]
        exact_mod_cast hIn
      · rintro ⟨v, hv, rfl⟩
        rw [key] at hv
        exact ⟨ne_bot_of_coprime hNtop (Φ v).2.1, (Φ v).2.1, by exact_mod_cast hv, (Φ v).2.2⟩
    rw [aRay, hset, Set.ncard_image_of_injective _ (Subtype.val_injective.comp Φ.injective)]

end GlobalTheory.Hk.RayForm
