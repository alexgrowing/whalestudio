import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

theorem UpperTheory.Gal.TypesAndIwahori.indSupp :
    UpperTheory.Gal.TypesAndIwahori.IndSupp := by
  intro G W _ _ _ _ _ P C σ u hC hu
  classical
  let φ : G → W := fun g => if h : ∃ p : P, ∃ c ∈ C, g = ↑p * c then σ h.choose u else 0
  have key : ∀ (p : P) (c : G), c ∈ C → φ (↑p * c) = σ p u := by
    intro p c hc
    have h : ∃ p' : P, ∃ c' ∈ C, (↑p * c : G) = ↑p' * c' := ⟨p, c, hc, rfl⟩
    simp only [φ, dif_pos h]
    obtain ⟨c', hc', hpc⟩ := h.choose_spec
    have hq : ((h.choose⁻¹ * p : P) : G) ∈ C := by
      have e : ((h.choose⁻¹ * p : P) : G) = c' * c⁻¹ := by
        push_cast
        rw [eq_mul_inv_iff_mul_eq, mul_assoc]
        exact (congrArg _ hpc).trans (inv_mul_cancel_left _ _)
      rw [e]
      exact C.mul_mem hc' (C.inv_mem hc)
    have hfix := hu _ hq
    calc σ h.choose u = σ h.choose (σ (h.choose⁻¹ * p) u) := by rw [hfix]
      _ = σ p u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have zero : ∀ g : G, (¬∃ p : P, ∃ c ∈ C, g = ↑p * c) → φ g = 0 := by
    intro g hg
    simp only [φ, dif_neg hg]
  have memInd : φ ∈ indSpace P σ := by
    show ∀ (h : P) (g : G), φ (↑h * g) = σ h (φ g)
    intro h g
    by_cases hg : ∃ p : P, ∃ c ∈ C, g = ↑p * c
    · obtain ⟨p, c, hc, rfl⟩ := hg
      rw [← mul_assoc, ← Subgroup.coe_mul, key _ _ hc, key _ _ hc, map_mul, Module.End.mul_apply]
    · have hhg : ¬∃ p : P, ∃ c ∈ C, ↑h * g = ↑p * c := by
        rintro ⟨p, c, hc, hpc⟩
        exact hg ⟨h⁻¹ * p, c, hc, by rw [Subgroup.coe_mul, mul_assoc, ← hpc, Subgroup.coe_inv, inv_mul_cancel_left]⟩
      rw [zero _ hg, zero _ hhg, map_zero]
  have smooth : (⟨φ, memInd⟩ : indSpace P σ) ∈ smoothPart (ind P σ) := by
    apply mem_smoothPart_of_nhds
    refine Filter.mem_of_superset (hC.mem_nhds C.one_mem) ?_
    intro c hc
    show (ind P σ c) ⟨φ, memInd⟩ = ⟨φ, memInd⟩
    apply Subtype.ext
    funext x
    show φ (x * c) = φ x
    by_cases hx : ∃ p : P, ∃ c' ∈ C, x = ↑p * c'
    · obtain ⟨p, c', hc', rfl⟩ := hx
      rw [mul_assoc, key _ _ (C.mul_mem hc' hc), key _ _ hc']
    · have hxc : ¬∃ p : P, ∃ c' ∈ C, x * c = ↑p * c' := by
        rintro ⟨p, c', hc', hpc⟩
        exact hx ⟨p, c' * c⁻¹, C.mul_mem hc' (C.inv_mem hc), by rw [← mul_assoc, ← hpc, mul_inv_cancel_right]⟩
      rw [zero _ hx, zero _ hxc]
  exact ⟨⟨⟨φ, memInd⟩, smooth⟩, fun p c hc => key p c hc, fun g hg => zero g hg⟩
