import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.Model

theorem normOne_seven_one_two : NormOne 7 1 2 := by
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;> norm_num

theorem normOne_seven_two : NormOne 7 2 29 := by
  refine ⟨2, 4, ?_, ?_, ?_⟩ <;> norm_num

theorem normOne_dvd {d M p : ℕ} (hd : d % 4 = 3) (h : NormOne d M p) : (M : ℤ) ∣ (p : ℤ) - 1 := by
  obtain ⟨A, B, hN, ⟨b, rfl⟩, ⟨c, hc⟩⟩ := h
  obtain rfl : A = 2 + M * b + 2 * M * c := by linear_combination hc
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e - 1 := ⟨((d : ℤ) + 1) / 4, by omega⟩
  refine ⟨b + 2 * c + M * (c * (b + c) + e * b ^ 2), ?_⟩
  have h4 : 4 * ((p : ℤ) - 1) = 4 * ((M : ℤ) * (b + 2 * c + M * (c * (b + c) + e * b ^ 2))) := by
    linear_combination (-1 : ℤ) * hN + ((M : ℤ) ^ 2 * b ^ 2) * he
  linarith

theorem not_normOne : ¬ NormOne 7 2 2 := by
  rintro ⟨A, B, h1, ⟨b, rfl⟩, -⟩
  push_cast at h1
  have h2 : A ≤ 2 := by nlinarith [sq_nonneg b]
  have h3 : -2 ≤ A := by nlinarith [sq_nonneg b]
  have h4 : b ≤ 0 := by nlinarith [sq_nonneg A]
  have h5 : 0 ≤ b := by nlinarith [sq_nonneg A]
  interval_cases A <;> interval_cases b <;> norm_num at h1

theorem span_mem_principalRayGroup_top {K : Type} [Field K] [NumberField K] (a : 𝓞 K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    I ∈ rayP (⊤ : Ideal (𝓞 K)) :=
  Subgroup.subset_closure ⟨a, Submodule.mem_top, h⟩

theorem mem_rayI_of_coprime {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) :
    J ≠ 0 → J ⊔ 𝔮 = ⊤ → ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) → I ∈ rayI 𝔮 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ u hu =>
    intro _ _ I hI
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hI1 : I = 1 := Units.ext (by rw [hI, FractionalIdeal.coeIdeal_top, Units.val_one])
    rw [hI1]
    exact one_mem _
  | h₃ a P ha hP ih =>
    intro _ hcop I hI
    have hP0 : P ≠ 0 := hP.ne_zero
    have hPq : ¬ P ∣ 𝔮 := by
      intro hd
      apply hP.not_isUnit
      rw [Ideal.isUnit_iff, eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left (Ideal.le_of_dvd hd)
    have hacop : a ⊔ 𝔮 = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le_sup_right Ideal.mul_le_right _
    have hPf : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hP0
    have haf : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha
    have hI' : I = Units.mk0 _ hPf * Units.mk0 _ haf := Units.ext (by
      rw [hI, Units.val_mul, Units.val_mk0, Units.val_mk0, FractionalIdeal.coeIdeal_mul])
    have hu : Units.mk0 _ hPf ∈ rayI 𝔮 :=
      Subgroup.subset_closure ⟨⟨P, Ideal.isPrime_of_prime hP, hP0⟩, hPq, rfl⟩
    rw [hI']
    exact Subgroup.mul_mem _ hu (ih ha hacop _ rfl)

theorem principalRayGroup_le_coprimeIdealGroup {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : rayP 𝔮 ≤ rayI 𝔮 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro I ⟨a, ha, hI⟩
  refine mem_rayI_of_coprime 𝔮 _ ?_ ?_ I hI
  · intro h0
    apply I.ne_zero
    rw [hI, h0]
    exact FractionalIdeal.coeIdeal_bot
  · rw [Ideal.eq_top_iff_one]
    have hmem : a - (a - 1) ∈ Ideal.span {a} ⊔ 𝔮 :=
      Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right ha)
    simpa using hmem

private theorem finite_zeros_in_strip_box_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (t T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := t - T) (b := t + T))) (by
      rintro ρ ⟨h1, h2, h3, -⟩
      rw [abs_le] at h3
      exact ⟨⟨h1.le, h2.le⟩, ⟨by linarith, by linarith⟩⟩)
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x)
    (frequently_nhdsWithin_iff.mpr ((accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2.2.2, hy.1⟩))
  obtain ⟨z, hz⟩ := hne
  exact hz (hzero (Set.mem_univ z))

theorem zerosIn_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t T : ℝ) :
    (zerosIn χ t T).Finite :=
  finite_zeros_in_strip_box_of_differentiable (DirichletCharacter.differentiable_LFunction hχ)
    ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl hχ) (by norm_num)⟩ t T

private theorem finite_zeros_in_strip_box_of_differentiable' {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (t T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := t - T) (b := t + T))) (by
      rintro ρ ⟨h1, h2, h3, -⟩
      rw [abs_le] at h3
      exact ⟨⟨h1.le, h2.le⟩, ⟨by linarith, by linarith⟩⟩)
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x)
    (frequently_nhdsWithin_iff.mpr ((accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2.2.2, hy.1⟩))
  obtain ⟨z, hz⟩ := hne
  exact hz (hzero (Set.mem_univ z))

theorem zerosIn_finite_one {q : ℕ} [NeZero q] (t T : ℝ) :
    (zerosIn (1 : DirichletCharacter ℂ q) t T).Finite := by
  refine (finite_zeros_in_strip_box_of_differentiable' (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
    ⟨1, DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q⟩ t T).subset ?_
  rintro ρ ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  have hρ : ρ ≠ 1 := by rintro rfl; simp at h2
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ]
  rw [show DirichletCharacter.LFunctionTrivChar q ρ = 0 from h4, mul_zero]

theorem zmult_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (h : DirichletCharacter.LFunction χ ρ = 0) : 0 < zmult χ ρ := by
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ => hd.analyticAt z
    have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ ρ) ht
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl hχ)
      (by norm_num) (hz (Set.mem_univ 2))
  have h0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    (hd.analyticAt ρ).analyticOrderAt_ne_zero.mpr h
  show 0 < analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
  rw [Nat.pos_iff_ne_zero]
  intro h'
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, h', Nat.cast_zero]

end GlobalTheory.Mem.An.Model
