import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

section

variable {E : Type} [Field E] [NumberField E] {cj : E → E} {Y : Type} [AddCommGroup Y]
  [Module (𝓞 E) Y]

theorem two_mul_form_half_unit (hcj : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) (w₀ : 𝓞 E)
    (hw : (w₀ : E) + cj w₀ = 1) (γ : SymB cj Y) (a : Y) :
    2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
  obtain ⟨w', hw'⟩ := hcj w₀
  have mem : (∀ a d : Y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
      ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
        (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := γ.2
  have h1 : w₀ + w' = 1 := by
    apply RingOfIntegers.ext
    first
      | (push_cast; rw [hw', hw])
      | simp [hw', hw]
  have h2 : (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w' • a) a := by
    rw [mem.2 w₀ w' hw' a a, mem.1]
  have h3 : (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) ((w₀ + w') • a) a = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a := by
    rw [h1, one_smul]
  rw [add_smul, map_add, LinearMap.add_apply, ← h2] at h3
  linarith

end

theorem bil_rad {Y : Type} [AddCommGroup Y] (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)
    (hsym : ∀ a b, γ a b = γ b a) (hpsd : ∀ a, 0 ≤ γ a a) (a : Y) (ha : γ a a = 0) (y : Y) :
    γ a y = 0 := by
  have key : ∀ n : ℤ, 0 ≤ (n : ℝ) * γ a y + (n : ℝ) * γ a y + γ y y := by
    intro n
    have h := hpsd (n • a + y)
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, zsmul_eq_mul, ha,
      hsym y a, mul_zero, zero_add] at h
    linarith
  by_contra hs
  obtain ⟨N, hN⟩ := exists_nat_gt (γ y y / (2 * |γ a y|))
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have h := key N
    rw [abs_of_neg hneg, div_lt_iff₀ (by linarith)] at hN
    push_cast at h
    nlinarith
  · have h := key (-(N : ℤ))
    rw [abs_of_pos hpos, div_lt_iff₀ (by linarith)] at hN
    push_cast at h
    nlinarith

theorem phiCSpan_holds : PhiCSpanStatement := by
  intro E _ _ cj hcj Y _ _ w₀ hw β hβ k x hx
  unfold phiC
  let l : SymB cj Y →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i)
      map_add' := fun γ γ' => by simp [Finset.sum_add_distrib]
      map_smul' := fun r γ => by simp [Finset.mul_sum] }
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨l', -, hpos, he⟩
    by_cases h0 : β = 0
    · rw [he, h0, map_zero]
    · rw [he]
      exact (hpos β hβ h0).le
  · refine ⟨l, ?_, ?_, rfl⟩
    · intro γ hγ
      choose z hz using fun i => hγ (w₀ • x i) (x i)
      refine ⟨∑ i, z i, ?_⟩
      show ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) = ((∑ i, z i : ℤ) : ℝ)
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun i _ => hz i
    · intro γ hγ hne
      have mem : (∀ a d : Y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
          ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
            (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := γ.2
      have hsum : ∀ i, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) =
          (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x i) := fun i => two_mul_form_half_unit hcj w₀ hw γ (x i)
      have hnn : ∀ i, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i) := fun i => by
        have := hγ (x i)
        linarith [hsum i]
      show 0 < ∑ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x i) (x i)
      rcases (Finset.sum_nonneg fun i _ => hnn i).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        apply hne
        have hz : ∀ i, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x i) = 0 := by
          intro i
          have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp heq.symm i
            (Finset.mem_univ i)
          linarith [hsum i]
        have hrad : ∀ i y, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) y = 0 :=
          fun i y => bil_rad _ mem.1 hγ (x i) (hz i) y
        have hspan : ∀ u ∈ Submodule.span (𝓞 E) (Set.range x), ∀ y,
            (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) u y = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu =>
            obtain ⟨i, rfl⟩ := hu
            exact hrad i
          | zero => intro y; simp
          | add u v _ _ hu hv => intro y; simp [hu y, hv y]
          | smul c u _ hu =>
            intro y
            obtain ⟨c', hc'⟩ := hcj c
            rw [mem.2 c c' hc' u y]
            exact hu _
        apply Subtype.ext
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        obtain ⟨n, hn, hny⟩ := hx y
        have h1 := hspan _ hny z
        simp only [map_nsmul, map_zsmul, LinearMap.smul_apply, nsmul_eq_mul, zsmul_eq_mul] at h1
        rw [show ((0 : SymB cj Y) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) = 0 from rfl, LinearMap.zero_apply,
          LinearMap.zero_apply]
        rcases mul_eq_zero.mp h1 with h | h
        · first
            | exact absurd h (Nat.cast_ne_zero.mpr hn.ne')
            | exact absurd h (Int.cast_ne_zero.mpr hn.ne')
        · exact h

end Formalism.MainNotions.ModuliIntegralCharts.H1
