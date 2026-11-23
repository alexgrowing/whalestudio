import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.JSW.Central

def centralFns (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω : HChar E) :
    Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
  add_mem' hF hG z g := by simp [hF z g, hG z g, mul_add]
  zero_mem' _ _ := by simp
  smul_mem' c F hF z g := by simp [hF z g, mul_left_comm]

theorem apply_scalar (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (ω : HChar E) (hω : π.HasCentChar ω) (φ : Sm E a) (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspan π)
    (z : Neutral.B1.Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  have hc := CuspSub.hasCentral_iff.2 hω
  have hle : GlobalTheory.JSW.mspan π ≤ centralFns E a ω := by
    refine sInf_le ⟨fun ψ hψ z g => hc.apply hψ z g, fun F hF h z g => ?_, fun F hF f _ z g => ?_,
      fun F hF r f z g => ?_⟩
    · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
      rw [mul_assoc]; exact hF z _
    · change GlobalTheory.JSW.smoothInf f F (GeneralLinearGroup.scalar (Fin a) z * g) = _ * GlobalTheory.JSW.smoothInf f F g
      rw [← GlobalTheory.JSW.smoothInf_left]
      have e : (fun x => F (GeneralLinearGroup.scalar (Fin a) z * x)) = ((ω.1 z : ℂˣ) : ℂ) • F :=
        funext fun x => hF z x
      rw [e, GlobalTheory.JSW.smoothInf_smul]; rfl
    · change GlobalTheory.JSW.colConv r f F (GeneralLinearGroup.scalar (Fin a) z * g) = _ * GlobalTheory.JSW.colConv r f F g
      simp only [GlobalTheory.JSW.colConv, mul_assoc]
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [hF z]; ring
  rcases hφ with h | h
  · exact hc.apply h z g
  · exact hle h z g

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (ω : HChar E), π.HasCentChar ω → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspan π) → ∀ (z : Neutral.B1.Ideles E) (g : GA E a), φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g :=
  fun E _ _ _ a π ω hω φ hφ z g => apply_scalar E a π ω hω φ hφ z g

end GlobalTheory.JSW.Central
