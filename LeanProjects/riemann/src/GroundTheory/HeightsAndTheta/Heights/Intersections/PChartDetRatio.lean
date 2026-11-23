import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StChartDetRatio
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem ChartDetRatio.mem_adjoin_of_mem_chartRing {Ω : Type} [Field Ω] [CharZero Ω] {ι : Type} (x : ι → Ω)
    (i₀ : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i₀) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin ℚ _ hy
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem ChartDetRatio.detE_sum {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (a a' : Fin 2 → Ω) :
    T.detE e (∑ q, a q • b q) (∑ q, a' q • b q) = (a 0 * a' 1 - a 1 * a' 0) * T.detE e (b 0) (b 1) := by
  simp only [T.detE, Fin.sum_univ_two, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

theorem ChartDetRatio.detE_ne_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    (e : Module.Basis (Fin 2) Ω E) (b : Fin 2 → E) (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) : T.detE e (b 0) (b 1) ≠ 0 := by
  have hu : IsUnit (e.det b) := (Module.Basis.is_basis_iff_det e).1 ⟨hli, hsp⟩
  have h : e.det b = T.detE e (b 0) (b 1) := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply, T.detE]
    ring
  rw [← h]
  exact hu.ne_zero

theorem ChartDetRatio.proof : ChartDetRatio.Statement := by
  intro Ω _ _ ι ν _ _ E _ _ x B e δ i₀ hx hδ
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  have hR : ∀ a ∈ chartRing ℤ x i₀, a ∈ F := fun a ha => ChartDetRatio.mem_adjoin_of_mem_chartRing x i₀ ha
  obtain ⟨k, f, c, hf, -, hcf, hb⟩ := B.frame i₀ hx
  obtain ⟨l₁, hl₁⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hcf
  obtain ⟨b, hbli, hbsp, hbiff⟩ := hb l₁
  have hfF : f l₁ ∈ F := hR _ (hf l₁)
  have hcoord : ∀ u ∈ B.lat i₀, ∃ a : Fin 2 → Ω, (∀ q, a q ∈ F) ∧ u = ∑ q, a q • b q := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := (hbiff u).1 ⟨0, by simpa using hu⟩
    refine ⟨a, fun q => ?_, rfl⟩
    obtain ⟨n, hn⟩ := ha q
    have h2 : a q = (f l₁ ^ n)⁻¹ * (f l₁ ^ n * a q) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl₁), one_mul]
    rw [h2]
    exact mul_mem (inv_mem (pow_mem hfF n)) (hR _ hn)
  set D := T.detE e (b 0) (b 1) with hDdef
  have hD : D ≠ 0 := ChartDetRatio.detE_ne_zero e b hbli hbsp
  have hdet : ∀ u ∈ B.lat i₀, ∀ w ∈ B.lat i₀, ∃ s ∈ F, T.detE e u w = D * s := by
    intro u hu w hw
    obtain ⟨a, ha, rfl⟩ := hcoord u hu
    obtain ⟨a', ha', rfl⟩ := hcoord w hw
    refine ⟨a 0 * a' 1 - a 1 * a' 0,
      sub_mem (mul_mem (ha 0) (ha' 1)) (mul_mem (ha 1) (ha' 0)), ?_⟩
    rw [ChartDetRatio.detE_sum, mul_comm]
  have hspan : ∀ y ∈ Submodule.span (chartRing ℤ x i₀)
      {d | ∃ u ∈ B.lat i₀, ∃ w ∈ B.lat i₀, d = x i₀ * T.detE e u w}, ∃ s ∈ F, y = x i₀ * D * s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, w, hw, rfl⟩ := hy
      obtain ⟨s, hs, h⟩ := hdet u hu w hw
      exact ⟨s, hs, by rw [h]; ring⟩
    | zero => exact ⟨0, zero_mem _, by ring⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨s + t, add_mem hs ht, by ring⟩
    | smul a y _ hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      refine ⟨(a : Ω) * s, mul_mem (hR _ a.2) hs, ?_⟩
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
  have hδs : ∀ l, ∃ s ∈ F, δ l = x i₀ * D * s := fun l => hspan _ ((hδ i₀ hx).1 l)
  have hbmem : ∀ q, ∃ n : ℕ, f l₁ ^ n • b q ∈ B.lat i₀ := by
    intro q
    refine (hbiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q' = q
      · subst h
        simp [one_mem (chartRing ℤ x i₀)]
      · simp [h, zero_mem (chartRing ℤ x i₀)]
    · fin_cases q <;> simp
  obtain ⟨n0, h0⟩ := hbmem 0
  obtain ⟨n1, h1⟩ := hbmem 1
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, δ l₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hm := (hδ i₀ hx).2 _ h0 _ h1
    have hbot : Submodule.span (chartRing ℤ x i₀) (Set.range fun l => (x i₀)⁻¹ * δ l) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      simp [h l]
    rw [hbot, Submodule.mem_bot] at hm
    have hsm : T.detE e (f l₁ ^ n0 • b 0) (f l₁ ^ n1 • b 1) = f l₁ ^ n0 * f l₁ ^ n1 * D := by
      simp only [T.detE, map_smul, Finsupp.smul_apply, smul_eq_mul, hDdef]
      ring
    rw [hsm] at hm
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hl₁) (pow_ne_zero _ hl₁)) hD hm
  obtain ⟨s₀, hs₀, hδ₀⟩ := hδs l₀
  have hs₀ne : s₀ ≠ 0 := by
    rintro rfl
    exact hl₀ (by rw [hδ₀, mul_zero])
  refine ⟨l₀, hl₀, fun l => ?_⟩
  obtain ⟨s, hs, hδl⟩ := hδs l
  rw [hδl, hδ₀, mul_div_mul_left _ _ (mul_ne_zero hx hD)]
  exact div_mem hs hs₀

end

end GroundTheory.Heights₂.Heights.Inter
