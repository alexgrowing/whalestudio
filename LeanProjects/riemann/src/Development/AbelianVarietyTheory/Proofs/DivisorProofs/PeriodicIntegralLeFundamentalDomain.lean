import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

theorem lattice_vaddInvariant_volume (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) :
    VAddInvariantMeasure Λ (Fin g → ℂ) volume :=
  ⟨fun c s _ => by
    show volume ((fun x => (c : Fin g → ℂ) + x) ⁻¹' s) = volume s
    exact measure_preimage_add volume _ s⟩

theorem lintegral_le_of_injects_fundamentalDomain :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (F : (Fin g → ℂ) → ℝ)
      (Fd U : Set (Fin g → ℂ)), Continuous F → (∀ (l : Λ) z, F (z + l) = F z) →
      IsAddFundamentalDomain Λ Fd volume → MeasurableSet U →
      (∀ u ∈ U, ∀ v ∈ U, u - v ∈ Λ → u = v) →
      ∫⁻ w in U, ENNReal.ofReal (F w) ≤ ∫⁻ z in Fd, ENNReal.ofReal (F z) := by
  intro g Λ _ F Fd U _ hper hFd hU hinj
  haveI : Countable Λ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  haveI := lattice_vaddInvariant_volume g Λ
  rw [hFd.setLIntegral_eq_tsum' (fun w => ENNReal.ofReal (F w)) U]
  have key : ∀ (l : Λ) (x : Fin g → ℂ), F (-l +ᵥ x) = F x := by
    intro l x
    have h := hper l (-l +ᵥ x)
    have e : (-l +ᵥ x) + (l : Fin g → ℂ) = x := by
      show (((-l : Λ) : Fin g → ℂ) + x) + (l : Fin g → ℂ) = x
      rw [Submodule.coe_neg]; abel
    rw [e] at h
    exact h.symm
  simp only [key]
  rw [← lintegral_iUnion₀]
  · exact lintegral_mono_set (Set.iUnion_subset fun l => Set.inter_subset_right)
  · intro l
    exact (hU.const_vadd l).nullMeasurableSet.inter hFd.nullMeasurableSet
  · intro a b hab
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    rintro x ⟨hxa, _⟩ ⟨hxb, _⟩
    obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.1 hxa
    obtain ⟨v, hv, hv'⟩ := Set.mem_vadd_set.1 hxb
    have hv'' : (b : Fin g → ℂ) + v = (a : Fin g → ℂ) + u := hv'
    have hmem : u - v ∈ Λ := by
      have : u - v = (b : Fin g → ℂ) - a := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm u, hv'', add_comm]
      rw [this]
      exact Λ.sub_mem b.2 a.2
    have huv := hinj u hu v hv hmem
    subst huv
    apply hab
    apply Subtype.ext
    exact (add_right_cancel hv'').symm

end GlobalTheory
