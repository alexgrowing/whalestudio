import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

open NumberField IsDedekindDomain GlobalTheory.TrueGeo

namespace GlobalTheory.TrueGeo.ExtOfEmb

variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_isIntegral_int {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

section Field

variable {F : Type} [Field F] [NumberField F]

theorem norm_int_le (φ : F →+* ℂ_[p]) (y : 𝓞 F) : ‖φ (y : F)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int φ (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (φ : F →+* ℂ_[p]) : Ideal (𝓞 F) where
  carrier := {y | ‖φ (y : F)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : φ ((a + b : 𝓞 F) : F) = φ (a : F) + φ (b : F) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : φ ((c • a : 𝓞 F) : F) = φ (c : F) * φ (a : F) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le φ c
    nlinarith [norm_nonneg (φ (c : F)), norm_nonneg (φ (a : F))]

theorem mem_smallIdeal (φ : F →+* ℂ_[p]) (y : 𝓞 F) : y ∈ smallIdeal φ ↔ ‖φ (y : F)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (φ : F →+* ℂ_[p]) : (smallIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : φ ((a * b : 𝓞 F) : F) = φ (a : F) * φ (b : F) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon.1, hcon.2]

theorem natCast_mem_smallIdeal (φ : F →+* ℂ_[p]) : (p : 𝓞 F) ∈ smallIdeal φ := by
  rw [mem_smallIdeal]
  simpa using norm_p_lt_one (p := p)

def place (φ : F →+* ℂ_[p]) : HeightOneSpectrum (𝓞 F) where
  asIdeal := smallIdeal φ
  isPrime := smallIdeal_isPrime φ
  ne_bot := by
    intro h
    have hp := natCast_mem_smallIdeal φ
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hp

noncomputable def normAbv (φ : F →+* ℂ_[p]) : AbsoluteValue F ℝ :=
  (NormedField.toAbsoluteValue ℂ_[p]).comp φ.injective

theorem normAbv_apply (φ : F →+* ℂ_[p]) (x : F) : normAbv φ x = ‖φ x‖ := rfl

theorem isEquiv (φ : F →+* ℂ_[p]) :
    (NumberField.HeightOneSpectrum.adicAbv F (place φ)).IsEquiv (normAbv φ) := by
  set v := place φ
  have hb := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  show (v.adicAbv hb).IsEquiv (normAbv φ)
  have hφ : ∀ x : 𝓞 F, ‖φ (x : F)‖ ≤ 1 ∧ (‖φ (x : F)‖ < 1 ↔ x ∈ v.asIdeal) :=
    fun x => ⟨norm_int_le φ x, Iff.rfl⟩
  have hd : ∀ d : 𝓞 F, d ∉ v.asIdeal → ‖φ (algebraMap (𝓞 F) F d)‖ = 1 := fun d hd =>
    le_antisymm (hφ d).1 (not_lt.1 fun h => hd ((hφ d).2.1 h))
  have hl : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := natCast_mem_smallIdeal φ
  have hl0 : algebraMap (𝓞 F) F ((p : ℕ) : 𝓞 F) ≠ 0 := by
    rw [map_natCast]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine AbsoluteValue.isEquiv_of_lt_one_imp ?_ ?_
  · exact ⟨algebraMap (𝓞 F) F ((p : ℕ) : 𝓞 F), hl0, ((v.adicAbv_coe_lt_one_iff (K := F) hb _).2 hl).ne⟩
  · intro x hx
    obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (R := 𝓞 F) (K := F) v x
    · have hdv : (d : 𝓞 F) ∉ v.asIdeal := d.2
      have hAd := (v.adicAbv_coe_eq_one_iff (K := F) hb (d : 𝓞 F)).2 hdv
      have hAn : v.adicAbv hb (algebraMap (𝓞 F) F n) < 1 := by
        rw [← h, map_mul, hAd, mul_one]; exact hx
      have hn : n ∈ v.asIdeal := (v.adicAbv_coe_lt_one_iff (K := F) hb n).1 hAn
      have h1 : ‖φ (algebraMap (𝓞 F) F n)‖ < 1 := (hφ n).2.2 hn
      have h2 := hd d hdv
      rw [normAbv_apply]
      have h3 : ‖φ x‖ * ‖φ (algebraMap (𝓞 F) F d)‖ = ‖φ (algebraMap (𝓞 F) F n)‖ := by
        rw [← norm_mul, ← map_mul, h]
      rw [h2, mul_one] at h3
      rw [h3]; exact h1
    · exfalso
      have hAd := (v.adicAbv_coe_eq_one_iff (K := F) hb (d : 𝓞 F)).2 d.2
      have hAn := v.adicAbv_coe_le_one (K := F) hb n
      have h4 : v.adicAbv hb x * v.adicAbv hb (algebraMap (𝓞 F) F n) = 1 := by
        rw [← map_mul, h, hAd]
      have h5 := mul_lt_one_of_nonneg_of_lt_one_left (AbsoluteValue.nonneg _ _) hx hAn
      linarith

end Field

section Closure

variable {K : Type} [Field K]

noncomputable def powAbv (ι : K →+* ℂ_[p]) (c : ℝ) (hc : 0 < c) : AbsoluteValue K ℝ where
  toFun x := ‖ι x‖ ^ c
  map_mul' x y := by
    simp only [map_mul, norm_mul]
    exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  nonneg' x := Real.rpow_nonneg (norm_nonneg _) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (norm_nonneg _) hc.ne', norm_eq_zero, map_eq_zero]
  add_le' x y := by
    rw [map_add]
    calc ‖ι x + ι y‖ ^ c ≤ (max ‖ι x‖ ‖ι y‖) ^ c :=
          Real.rpow_le_rpow (norm_nonneg _) (IsUltrametricDist.norm_add_le_max _ _) hc.le
      _ ≤ ‖ι x‖ ^ c + ‖ι y‖ ^ c := by
        rcases le_total ‖ι x‖ ‖ι y‖ with h | h
        · rw [max_eq_right h]; linarith [Real.rpow_nonneg (norm_nonneg (ι x)) c]
        · rw [max_eq_left h]; linarith [Real.rpow_nonneg (norm_nonneg (ι y)) c]

theorem powAbv_apply (ι : K →+* ℂ_[p]) (c : ℝ) (hc : 0 < c) (x : K) : powAbv ι c hc x = ‖ι x‖ ^ c := rfl

def ball (ι : K →+* ℂ_[p]) : ValuationSubring K where
  carrier := {z | ‖ι z‖ ≤ 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx
  mem_or_inv_mem' x := by
    simp only [Set.mem_setOf_eq, map_inv₀, norm_inv]
    rcases le_total ‖ι x‖ 1 with h | h
    · exact .inl h
    · exact .inr (inv_le_one_of_one_le₀ h)

theorem mem_ball (ι : K →+* ℂ_[p]) (z : K) : z ∈ ball ι ↔ ‖ι z‖ ≤ 1 := Iff.rfl

end Closure

theorem exists_ext : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
    (ι : AlgebraicClosure F →+* ℂ_[p]), ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v),
      (p : 𝓞 F) ∈ v.asIdeal ∧ ∀ a, ‖ι a‖ ≤ 1 ↔ a ∈ e.O := by
  intro F _ _ p _ ι
  let φ : F →+* ℂ_[p] := ι.comp (algebraMap F _)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (isEquiv φ).symm
  refine ⟨place φ, ⟨powAbv ι c hc, fun a => ?_, ball ι, fun x => ?_⟩, natCast_mem_smallIdeal φ, fun a => Iff.rfl⟩
  · rw [powAbv_apply, ← congrFun hce a, normAbv_apply]
    rfl
  · rw [mem_ball, powAbv_apply, ← Real.rpow_le_rpow_iff (norm_nonneg _) zero_le_one hc, Real.one_rpow]

end GlobalTheory.TrueGeo.ExtOfEmb
