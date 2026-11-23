import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem hilbert90_locallyConstant_cocycle :
    ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
      IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) →
        ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  intro K Ω _ _ _ _ _ w hw hc
  have h1 : w 1 = 1 := by
    apply Units.ext
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    have h' : ((w 1 : Ωˣ) : Ω) * 1 = (w 1 : Ω) * (w 1 : Ω) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ (w 1).ne_zero h').symm
  have hopen : IsOpen (w ⁻¹' {1}) := hw _
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 (hopen.mem_nhds (by simp [h1]))
  haveI := hfin
  obtain ⟨β, hβ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_of_cocycle (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) (fun h => w h.1) E
    (fun h hh => hE hh) (fun g h => Units.ext (by simp [hc]))
  refine ⟨β, fun g => ?_⟩
  have := congrArg Units.val (hβ ⟨g, Subgroup.mem_top g⟩)
  simpa [div_eq_mul_inv] using this

end GlobalTheory
