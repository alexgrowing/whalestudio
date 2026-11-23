import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfIsLocCompGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.RSHS.ProjectionSandwichLength

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

omit [IsTotallyComplex E] in

theorem eq_of_isAbsPow {ν ν' : HChar E} {s : ℝ} (h : ν.IsAbsPow s) (h' : ν'.IsAbsPow s) : ν = ν' := by
  have h0 : (ν * ν'⁻¹).IsAbsPow 0 := by
    refine ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
    · simp only [HChar.loc_mul, HChar.loc_inv, h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
    · have e : ν.val v = ν'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
      simp [HChar.val_mul, HChar.val_inv, e]
    · have e : ν.inf k = ν'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
      simp [HChar.inf_mul, HChar.inf_inv, e]
  exact mul_inv_eq_one.1 (GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow h0)

def SpehQuotUnique (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) : Prop :=
  ∀ (a d : ℕ) (π : CuspSub E a), π.IsUnitary → IsNormalised π → ∀ (h : ∑ _ : Fin d, a = N) (ν : Fin d → HChar E),
    (∀ i, (ν i).IsAbsPow (spehExp d i + a * spehExp d i)) →
    ∀ W W' : Submodule ℂ (Sm E N), IsStable W → IsStable W' →
      W < indForms h (fun i => π.twist (ν i)) → W' < indForms h (fun i => π.twist (ν i)) →
      (∀ Y, IsStable Y → W ≤ Y → Y < indForms h (fun i => π.twist (ν i)) → Y = W) →
      (∀ Y, IsStable Y → W' ≤ Y → Y < indForms h (fun i => π.twist (ν i)) → Y = W') → W = W'

section Quot

variable {I V : Submodule ℂ (Sm E N)} {f : Sm E N →ₗ[ℂ] Sm E N}

end Quot

end PositivityTheory.RSHS.ProjectionSandwichLength

end
