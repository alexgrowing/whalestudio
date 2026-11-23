import Mathlib
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FunctionalValuesNonempty

noncomputable section
open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.LeastExponentCompare
open scoped Pointwise

namespace GlobalTheory.LeastExponentProbe

variable {E : Type} [Field E] [NumberField E] {cj : E → E}
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def vals (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

theorem phiC_def (b : SymB cj Y) : phiC cj b = sInf (vals b) := rfl

theorem phiC_of_subsingleton [Subsingleton Y] (b : SymB cj Y) : phiC cj b = 0 := by
  rw [phiC_def]
  have hb : b = 0 := Subtype.ext (LinearMap.ext fun a => LinearMap.ext fun c => by
    rw [Subsingleton.elim a 0]; simp)
  have hsub : vals b ⊆ {0} := by
    rintro x ⟨l, -, -, rfl⟩
    rw [hb, map_zero]
    exact Set.mem_singleton _
  rcases Set.subset_singleton_iff_eq.1 hsub with he | he <;> simp [he]

private lemma nat_mul_mem_vals {b : SymB cj Y} {x : ℝ} (hx : x ∈ vals b) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * x ∈ vals b := by
  obtain ⟨l, h1, h2, rfl⟩ := hx
  refine ⟨(n : ℝ) • l, fun β hβ => ?_, fun β hβ hne => ?_, by simp⟩
  · obtain ⟨z, hz⟩ := h1 β hβ
    exact ⟨n * z, by simp [hz]⟩
  · have hl := h2 β hβ hne
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simpa using mul_pos hn' hl

theorem phiC_eq_zero_of_neg (b : SymB cj Y) {x : ℝ} (hx : x ∈ vals b) (hneg : x < 0) : phiC cj b = 0 := by
  rw [phiC_def]
  apply Real.sInf_of_not_bddBelow
  rintro ⟨m, hm⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (m / x)
  have hmem := nat_mul_mem_vals hx (n + 1) n.succ_pos
  have h1 : m ≤ ((n + 1 : ℕ) : ℝ) * x := hm hmem
  have h2 : ((n + 1 : ℕ) : ℝ) * x < m := by
    rw [← div_lt_iff_of_neg hneg]
    push_cast
    linarith
  linarith

theorem symB_eq_bot_of_apply_one (h : cj 1 = 0) : SymB cj Y = ⊥ := by
  refine eq_bot_iff.2 fun β hβ => (Submodule.mem_bot ℝ).2 ?_
  have hb := hβ.2 1 0 (by simp [h])
  ext a c
  simpa using hb a c

private lemma pos_mul_mem_vals_of_integral_eq_zero (h : ∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → β = 0)
    {b : SymB cj Y} {x : ℝ} (hx : x ∈ vals b) {c : ℝ} (hc : 0 < c) : c * x ∈ vals b := by
  obtain ⟨l, h1, h2, rfl⟩ := hx
  refine ⟨c • l, fun β hβ => ⟨0, ?_⟩, fun β hβ hne => ?_, by simp⟩
  · rw [h β hβ]
    simp
  · simpa using mul_pos hc (h2 β hβ hne)

theorem phiC_of_no_integral_form
    (h : ∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → β = 0) (b : SymB cj Y) :
    phiC cj b = 0 := by
  by_cases hneg : ∃ x ∈ vals b, x < 0
  · obtain ⟨x, hx, hx0⟩ := hneg
    exact phiC_eq_zero_of_neg b hx hx0
  push_neg at hneg
  have hbdd : BddBelow (vals b) := ⟨0, fun y hy => hneg y hy⟩
  rw [phiC_def]
  rcases (vals b).eq_empty_or_nonempty with he | hne
  · rw [he, Real.sInf_empty]
  refine le_antisymm ?_ (le_csInf hne fun y hy => hneg y hy)
  by_contra hlt
  push_neg at hlt
  obtain ⟨x, hx⟩ := hne
  have hxs : sInf (vals b) ≤ x := csInf_le hbdd hx
  have hxpos : 0 < x := lt_of_lt_of_le hlt hxs
  have hc : 0 < sInf (vals b) / (2 * x) := by positivity
  have hmem := pos_mul_mem_vals_of_integral_eq_zero h hx hc
  have hle := csInf_le hbdd hmem
  have hx0 : x ≠ 0 := hxpos.ne'
  have heq : sInf (vals b) / (2 * x) * x = sInf (vals b) / 2 := by
    field_simp
  linarith

private lemma vals_eq_functionalValues [IsCMField E] (b : SymB cj Y) : vals b = functionalValues b := by
  ext x
  constructor
  · rintro ⟨l, h1, h2, hx⟩
    exact ⟨l, ⟨h1, h2⟩, hx⟩
  · rintro ⟨l, ⟨h1, h2⟩, hx⟩
    exact ⟨l, h1, h2, hx⟩

section CM

variable [IsCMField E] [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem one_le_phiC (h : IsConj cj) (b : SymB cj Y)
    (hint : ∀ a c, ∃ z : ℤ, (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z)
    (hpos : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) (h0 : b ≠ 0) : 1 ≤ phiC cj b := by
  rw [phiC_def]
  refine le_csInf (by rw [vals_eq_functionalValues]; exact functionalValues_nonempty h b) ?_
  rintro x ⟨l, h1, h2, rfl⟩
  obtain ⟨z, hz⟩ := h1 b hint
  have hp := h2 b hpos h0
  rw [hz] at hp ⊢
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

def trForm (h : IsConj cj) : SymB cj (𝓞 E) := (formsEquiv (𝓞 E) h).symm (GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem.traceForm E)

end CM

end GlobalTheory.LeastExponentProbe

end
