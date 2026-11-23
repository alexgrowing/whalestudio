import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open GlobalTheory.UT

namespace GlobalTheory.TestFibre

theorem exists_val_le_of_sumV_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  classical
  intro F _ v X T _ χ cf ζ w α q hS hζ hχ hT hα hβ
  by_contra hcon
  have hw : ∀ t, (q : WithTop ℚ) < v (w t) := fun t => lt_of_not_ge fun h => hcon ⟨t, h⟩
  have hq : (q : WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
  have hne : ∀ t, χ t α ≠ 0 := fun t h => by
    have h1 := hχ t α
    rw [h, v.map_zero] at h1
    exact WithTop.top_ne_zero h1
  have hinv : ∀ t, v (χ t α)⁻¹ = 0 := fun t => by
    have h1 : v ((χ t α)⁻¹ * χ t α) = 0 := by rw [inv_mul_cancel₀ (hne t), v.map_one]
    rwa [v.map_mul, hχ t α, add_zero] at h1
  choose S hS' using fun t => hS t (q + 1)
  set U : Finset X := insert α (Finset.univ.biUnion S) with hU
  have hαU : α ∈ U := Finset.mem_insert_self _ _
  have hSU : ∀ t, S t ⊆ U := fun t x hx =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, hx⟩)
  have hq1 : (q : WithTop ℚ) < ((q + 1 : ℚ) : WithTop ℚ) := WithTop.coe_lt_coe.2 (by linarith)
  have hA : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, v.map_mul, hinv, hζ, zero_add, zero_add]; exact hw t
  have hB : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, hinv, zero_add]; exact hq1.trans_le (hS' t U (hSU t))
  have hC : (q : WithTop ℚ) < v (∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β) :=
    v.map_lt_sum hq fun β hb => by
      rcases hβ β (Finset.ne_of_mem_erase hb) with h | h
      · rw [h, zero_mul, v.map_zero]; exact WithTop.coe_lt_top q
      · rw [v.map_mul]
        have h0 : (0 : WithTop ℚ) ≤ v (∑ t, (χ t α)⁻¹ * χ t β) :=
          v.map_le_sum fun t _ => by rw [v.map_mul, hinv, hχ, add_zero]
        exact h.trans_le (le_add_of_nonneg_left h0)
  have e1 : ∑ t, (χ t α)⁻¹ * χ t α = ((Fintype.card T : ℕ) : F) := by
    rw [Finset.sum_congr rfl fun t _ => inv_mul_cancel₀ (hne t)]
    simp
  have e2 : ∑ t, (χ t α)⁻¹ * (∑ β ∈ U, χ t β * cf β) = ∑ β ∈ U, (∑ t, (χ t α)⁻¹ * χ t β) * cf β := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have e : ((Fintype.card T : ℕ) : F) * cf α =
      (∑ t, (χ t α)⁻¹ * (ζ t * w t)) +
        (-(∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) +
          -(∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e2, ← Finset.add_sum_erase U _ hαU, e1]
    ring
  have hfin : (q : WithTop ℚ) < v (((Fintype.card T : ℕ) : F) * cf α) := by
    rw [e]
    exact v.map_lt_add hA (v.map_lt_add (by rwa [v.map_neg]) (by rwa [v.map_neg]))
  rw [v.map_mul, hT, zero_add, hα] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.TestFibre
