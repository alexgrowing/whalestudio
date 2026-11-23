import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExistsSmallMemIdeal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmallNorm

open Module

theorem exists_pow_between (N f : ℕ) (hN : 1 ≤ N) (hf : 1 ≤ f) :
    ∃ r : ℕ, 1 ≤ r ∧ N ≤ r ^ f ∧ r ^ f ≤ 2 ^ f * N := by
  classical
  have hex : ∃ r : ℕ, N ≤ r ^ f := ⟨N, Nat.le_self_pow (by omega) N⟩
  have hP : N ≤ (Nat.find hex) ^ f := Nat.find_spec hex
  have hr0 : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, zero_pow (by omega)] at hP; omega
    · exact h
  refine ⟨Nat.find hex, hr0, hP, ?_⟩
  rcases Nat.eq_or_lt_of_le hr0 with h | h
  · rw [← h, one_pow]
    calc 1 ≤ 2 ^ f := Nat.one_le_two_pow
      _ ≤ 2 ^ f * N := Nat.le_mul_of_pos_right _ hN
  · have hlt : (Nat.find hex - 1) ^ f < N :=
      not_le.mp (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
    calc (Nat.find hex) ^ f ≤ (2 * (Nat.find hex - 1)) ^ f := Nat.pow_le_pow_left (by omega) f
      _ = 2 ^ f * (Nat.find hex - 1) ^ f := by rw [mul_pow]
      _ ≤ 2 ^ f * N := Nat.mul_le_mul_left _ hlt.le

theorem isCoprime_norm_of_eq {F : Type} [Field F] [NumberField F] (q : ℕ) (b y : 𝓞 F)
    (h : b = 1 + (q : 𝓞 F) * y) : IsCoprime (Algebra.norm ℤ b) (q : ℤ) := by
  classical
  have key : ((Algebra.norm ℤ b : ℤ) : ZMod q) = 1 := by
    rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis F), ← eq_intCast (Int.castRingHom (ZMod q)),
      RingHom.map_det, h, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]
    simp
  have hd : (q : ℤ) ∣ Algebra.norm ℤ b - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [key, sub_self]
  obtain ⟨m, hm⟩ := hd
  exact ⟨1, -m, by linarith⟩

theorem exists_small_coprime_norm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (q : ℕ), 1 ≤ q → ∃ C : ℕ,
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → IsCoprime I (Ideal.span {(q : 𝓞 F)}) →
      ∃ b ∈ I, b ≠ 0 ∧ IsCoprime (Algebra.norm ℤ b) (q : ℤ) ∧
        ∃ k : ℕ, IsTotPos (((k : F)) ^ 2 - (b : F) ^ 2) ∧ k ^ Module.finrank ℚ F ≤ C * Ideal.absNorm I := by
  intro F _ _ _ q hq
  classical
  have hf : 0 < finrank ℚ F := finrank_pos
  set D : ℝ := Real.sqrt |(discr F : ℝ)| with hD_def
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  set c₀ : ℝ := 3 * D ^ ((finrank ℚ F : ℝ)⁻¹) with hc₀_def
  have hc₀ : 0 ≤ c₀ := by positivity
  have habs : ∀ (τ : F →+* ℝ) (y : F), |τ y| = InfinitePlace.mk (Complex.ofRealHom.comp τ) y := by
    intro τ y
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  set C₂ : ℝ := ∑ i, ∑ w : InfinitePlace F, w (integralBasis F i) with hC₂_def
  have hC₂ : ∀ (τ : F →+* ℝ) i, |τ (integralBasis F i)| ≤ ∑ w : InfinitePlace F, w (integralBasis F i) := by
    intro τ i
    rw [habs]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w (integralBasis F i))
      (fun w _ => apply_nonneg w _) (Finset.mem_univ _)
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
  set K₀ : ℕ := ⌈(q : ℝ) * c₀ * (C₂ + 1)⌉₊ + 1 with hK₀_def
  refine ⟨K₀ ^ finrank ℚ F * 2 ^ finrank ℚ F, ?_⟩
  intro I hI hcop
  have hN : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.2 (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h))
  obtain ⟨r, hr1, hNr, hr2⟩ := exists_pow_between (Ideal.absNorm I) (finrank ℚ F) hN hf

  obtain ⟨a₀, ha₀I, ha₀0, ha₀⟩ := ReciprocityTheory.ChartRestriction.G.TB.Mink.exists_small_mem_ideal' F I hI
  have hsmall : ∀ τ : F →+* ℝ, |τ (a₀ : F)| ≤ c₀ * r := by
    intro τ
    have h1 := ha₀ (Complex.ofRealHom.comp τ)
    rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs] at h1
    refine h1.le.trans ?_
    have hNr' : (Ideal.absNorm I : ℝ) ≤ (r : ℝ) ^ finrank ℚ F := by exact_mod_cast hNr
    calc 3 * ((Ideal.absNorm I : ℝ) * D) ^ ((finrank ℚ F : ℝ)⁻¹)
        ≤ 3 * (((r : ℝ) ^ finrank ℚ F) * D) ^ ((finrank ℚ F : ℝ)⁻¹) := by gcongr
      _ = c₀ * r := by
          rw [Real.mul_rpow (by positivity) hD, Real.pow_rpow_inv_natCast (by positivity) hf.ne', hc₀_def]
          ring

  rw [Ideal.isCoprime_iff_add, Ideal.one_eq_top, Ideal.eq_top_iff_one, Ideal.add_eq_sup, Submodule.mem_sup] at hcop
  obtain ⟨x, hxI, z, hz, hxz⟩ := hcop
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hq0 : (q : F) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  set b₀ : 𝓞 F := (q : 𝓞 F) * a₀ with hb₀_def
  have hb₀F : (b₀ : F) = (q : F) * (a₀ : F) := by simp [hb₀_def]
  have ha₀F : (a₀ : F) ≠ 0 := by simpa using ha₀0
  have hb₀ : (b₀ : F) ≠ 0 := by rw [hb₀F]; exact mul_ne_zero hq0 ha₀F
  have hb₀I : b₀ ∈ I := Ideal.mul_mem_left _ _ ha₀I

  set zz : F := (x : F) / (b₀ : F) with hzz
  set c := (integralBasis F).repr zz with hc
  set t : 𝓞 F := ∑ i, ⌊c i⌋ • RingOfIntegers.basis F i with ht_def
  have hdec : zz - (t : F) = ∑ i, ((Int.fract (c i) : ℚ) : F) * integralBasis F i := by
    have h1 : zz = ∑ i, ((c i : ℚ) : F) * integralBasis F i := by
      conv_lhs => rw [← (integralBasis F).sum_repr zz]
      simp [Rat.smul_def, hc]
    have h2 : (t : F) = ∑ i, (((⌊c i⌋ : ℤ) : ℚ) : F) * integralBasis F i := by
      simp [ht_def, integralBasis_apply, zsmul_eq_mul]
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.fract, ← sub_mul]; push_cast; ring
  have hfr : ∀ τ : F →+* ℝ, |τ (zz - (t : F))| ≤ C₂ := by
    intro τ
    rw [hdec, map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_mul, map_ratCast, abs_mul]
    have e1 : |((Int.fract (c i) : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
      exact_mod_cast (Int.fract_lt_one _).le
    calc |((Int.fract (c i) : ℚ) : ℝ)| * |τ (integralBasis F i)| ≤ 1 * |τ (integralBasis F i)| := by
          gcongr
      _ ≤ _ := by rw [_root_.one_mul]; exact hC₂ τ i

  obtain ⟨s, hs0, hs⟩ : ∃ s : 𝓞 F, x - b₀ * s ≠ 0 ∧ ∀ τ : F →+* ℝ, |τ (zz - (s : F))| ≤ C₂ + 1 := by
    by_cases h0 : x - b₀ * t = 0
    · refine ⟨t + 1, ?_, fun τ => ?_⟩
      · intro h; apply ha₀0
        have : b₀ = 0 := by linear_combination h0 - h
        rw [hb₀_def] at this
        rcases mul_eq_zero.1 this with h' | h'
        · exact absurd (by exact_mod_cast h' : (q : F) = 0) hq0
        · exact h'
      · have : τ (zz - ((t + 1 : 𝓞 F) : F)) = τ (zz - (t : F)) - 1 := by
          push_cast; simp only [map_sub, map_add, map_one]; ring
        rw [this]
        calc |τ (zz - (t : F)) - 1| ≤ |τ (zz - (t : F))| + |(1 : ℝ)| := abs_sub _ _
          _ ≤ C₂ + 1 := by rw [abs_one]; linarith [hfr τ]
    · exact ⟨t, h0, fun τ => (hfr τ).trans (by linarith)⟩
  set b : 𝓞 F := x - b₀ * s with hb_def
  have hbI : b ∈ I := I.sub_mem hxI (Ideal.mul_mem_right _ _ hb₀I)
  have hbq : b = 1 + (q : 𝓞 F) * (-u - a₀ * s) := by
    rw [hb_def, hb₀_def]; linear_combination hxz
  have hbF : (b : F) = (b₀ : F) * (zz - (s : F)) := by
    rw [hzz, hb_def]; push_cast; field_simp
  have hbnd : ∀ τ : F →+* ℝ, |τ (b : F)| < (K₀ * r : ℕ) := by
    intro τ
    rw [hbF, map_mul, abs_mul, hb₀F, map_mul, map_natCast, abs_mul, Nat.abs_cast]
    have hr : (0 : ℝ) < r := by exact_mod_cast hr1
    have hK : (q : ℝ) * c₀ * (C₂ + 1) < K₀ := by
      rw [hK₀_def]; push_cast; linarith [Nat.le_ceil ((q : ℝ) * c₀ * (C₂ + 1))]
    calc (q : ℝ) * |τ (a₀ : F)| * |τ (zz - (s : F))| ≤ (q : ℝ) * (c₀ * r) * (C₂ + 1) := by
          gcongr
          · exact hsmall τ
          · exact hs τ
      _ = ((q : ℝ) * c₀ * (C₂ + 1)) * r := by ring
      _ < K₀ * r := by gcongr
      _ = ((K₀ * r : ℕ) : ℝ) := by push_cast; ring
  refine ⟨b, hbI, hs0, isCoprime_norm_of_eq q b _ hbq, K₀ * r, ?_, ?_⟩
  · intro τ
    have h := abs_lt.1 (hbnd τ)
    rw [map_sub, map_pow, map_pow, map_natCast]
    nlinarith [h.1, h.2]
  · rw [mul_pow, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ hr2

end GlobalTheory.SmallNorm
