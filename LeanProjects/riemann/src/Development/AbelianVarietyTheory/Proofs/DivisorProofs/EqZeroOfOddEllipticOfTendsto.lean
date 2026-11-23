import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

open Filter PeriodPair Polynomial
open scoped Topology

namespace GlobalTheory

private lemma eq_zero_of_tendsto_eval_cobounded {B : ℂ[X]} {l : Filter ℂ} [l.NeBot] {u : ℂ → ℂ}
    (hu : Tendsto u l (Bornology.cobounded ℂ))
    (h : Tendsto (fun z ↦ B.eval (u z)) l (𝓝 0)) : B = 0 := by
  by_cases hd : 0 < B.degree
  · exfalso
    have h1 := B.tendsto_norm_atTop hd (tendsto_norm_atTop_iff_cobounded.mpr hu)
    have h2 := h.norm
    exact h1.not_tendsto (disjoint_nhds_atTop _).symm h2
  · rw [eq_C_of_degree_le_zero (not_lt.mp hd)] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_nhds_unique tendsto_const_nhds h, C_0]

private lemma exists_eq_mul_of_three_roots {A : ℂ[X]} {a b c : ℂ} (hab : b ≠ a) (hac : c ≠ a)
    (hbc : c ≠ b) (ha : A.eval a = 0) (hb : A.eval b = 0) (hc : A.eval c = 0) :
    ∃ B : ℂ[X], A = (X - C a) * ((X - C b) * ((X - C c) * B)) := by
  obtain ⟨A₁, rfl⟩ := dvd_iff_isRoot.mpr ha
  have hb₁ : A₁.eval b = 0 := by simpa [sub_eq_zero, hab] using hb
  obtain ⟨A₂, rfl⟩ := dvd_iff_isRoot.mpr hb₁
  have hc₂ : A₂.eval c = 0 := by simpa [sub_eq_zero, hac, hbc] using hc
  obtain ⟨B, rfl⟩ := dvd_iff_isRoot.mpr hc₂
  exact ⟨B, rfl⟩

theorem eq_zero_of_odd_elliptic_of_tendsto : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  classical
  intro L f hd hp ho ht
  let g : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else f z ^ 2
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := fun z hz ↦ by
    refine ((hd z hz).pow 2).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [g, hw]
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := fun z l hl ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz, add_mem hz hl]
    · simp [g, hz, L.lattice.add_mem_iff_left hl, hp z l hz hl]
  have hge : ∀ z, g (-z) = g z := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz]
    · simp [g, hz, ho z hz]
  have hgt : Tendsto (fun z : ℂ ↦ z ^ 6 * g z) (𝓝[≠] 0) (𝓝 0) := by
    have h1 := ht.pow 2
    rw [zero_pow two_ne_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
    simp only [g, hw, if_false]
    ring
  have hgm : MeromorphicAt g 0 := by
    refine ⟨6, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_⟩
    · filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
      have := hgd w hw
      fun_prop
    · rw [continuousAt_iff_punctured_nhds]
      simpa using hgt
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hgm hgd hgp hge
  have hhalf : ∀ z ∉ L.lattice, z + z ∈ L.lattice → A.eval (℘[L] z) = 0 := fun z hz h2 ↦ by
    have h1 := hp (-z) (z + z) (by simpa using hz) h2
    rw [ho z hz, show -z + (z + z) = z by ring, CharZero.eq_neg_self_iff] at h1
    rw [← hA z hz]
    simp [g, h1]
  have key : ∀ a b : ℚ, (a * L.ω₁ + b * L.ω₂ : ℂ) ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 :=
    fun a b ↦ L.mul_ω₁_add_mul_ω₂_mem_lattice
  let p : ℚ → ℚ → ℂ := fun a b ↦ a * L.ω₁ + b * L.ω₂
  have padd : ∀ a b c d, p a b + p c d = p (a + c) (b + d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have psub : ∀ a b c d, p a b - p c d = p (a - c) (b - d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have pm : ∀ a b, p a b ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 := key
  have n1 : p (1 / 2) 0 ∉ L.lattice := by rw [pm]; norm_num
  have n2 : p 0 (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  have n3 : p (1 / 2) (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  obtain ⟨B, hB⟩ := exists_eq_mul_of_three_roots (A := A) (a := ℘[L] (p (1 / 2) 0))
    (b := ℘[L] (p 0 (1 / 2))) (c := ℘[L] (p (1 / 2) (1 / 2)))
    (by rw [Ne, weierstrassP_eq_iff L n2 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n2, padd, psub, pm, pm]; norm_num)
    (hhalf _ n1 (by rw [padd, pm]; norm_num))
    (hhalf _ n2 (by rw [padd, pm]; norm_num))
    (hhalf _ n3 (by rw [padd, pm]; norm_num))
  set a := ℘[L] (p (1 / 2) 0)
  set b := ℘[L] (p 0 (1 / 2))
  set c := ℘[L] (p (1 / 2) (1 / 2))
  let w : ℂ → ℂ := fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1
  have hw : AnalyticAt ℂ w 0 := by fun_prop
  have hw' : ∀ z ≠ 0, w z = z ^ 2 * ℘[L] z := fun z hz ↦ by
    simpa [hz, w] using (L.ite_eq_one_sub_sq_mul_weierstrassP 0 (zero_mem _) z).symm
  let q : ℂ → ℂ := fun z ↦ (w z - z ^ 2 * a) * ((w z - z ^ 2 * b) * (w z - z ^ 2 * c))
  have hq : ContinuousAt q 0 := by
    have := hw.continuousAt
    fun_prop
  have hq0 : q 0 = 1 := by simp [q, w]
  have hq1 : Tendsto q (𝓝[≠] 0) (𝓝 1) := hq0 ▸ hq.tendsto.mono_left nhdsWithin_le_nhds
  have hB0 : B = 0 := by
    refine eq_zero_of_tendsto_eval_cobounded (tendsto_weierstrassP_cobounded L (zero_mem _)) ?_
    have h1 := hgt.div hq1 one_ne_zero
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0, self_mem_nhdsWithin,
      hq1.eventually_ne one_ne_zero] with z hz hz0 hqz
    rw [Pi.div_apply, div_eq_iff hqz, hA z hz, hB]
    simp only [q, hw' z hz0, eval_mul, eval_sub, eval_X, eval_C]
    ring
  intro z hz
  have h1 := hA z hz
  rw [hB, hB0] at h1
  simpa [g, hz] using h1

end GlobalTheory
