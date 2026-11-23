import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.JSW

theorem mspanR_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ F ∈ GlobalTheory.JSW.mspanR π,
    ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g := by
  intro E _ _ _ a π
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g}
      add_mem' := by
        intro F G hF hG γ g
        simp only [Pi.add_apply, hF γ g, hG γ g]
      zero_mem' := by intro γ g; rfl
      smul_mem' := by
        intro c F hF γ g
        simp only [Pi.smul_apply, hF γ g] }
  have hS : mspanR π ≤ S := by
    refine sInf_le ⟨?_, ?_, ?_⟩
    · intro φ hφ γ g
      exact (π.cusp φ hφ).1.left γ g
    · intro F hF h γ g
      show F (ratGL E a γ * g * h) = F (g * h)
      rw [mul_assoc]; exact hF γ (g * h)
    · intro F hF X _ ν _ k γ' _ γ g
      show (∫ x, k x * F (ratGL E a γ * g * infGL E a (γ' x)) ∂ν) = ∫ x, k x * F (g * infGL E a (γ' x)) ∂ν
      congr 1
      funext x
      rw [mul_assoc, hF γ (g * infGL E a (γ' x))]
  intro F hF
  exact hS hF

end GlobalTheory.JSW
