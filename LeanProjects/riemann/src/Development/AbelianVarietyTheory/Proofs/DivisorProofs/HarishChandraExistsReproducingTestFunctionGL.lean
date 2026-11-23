import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroMemSphSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinityStatement

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_toUnits_Kinf : Continuous (Unitary.toUnits : Kinf E a → GL (Fin a) (Cinf E)) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩

theorem continuous_translate (φ : Sm E a) (g : GA E a) :
    Continuous fun y : GL (Fin a) (Cinf E) => φ.1 (g * infGL E a y) := by
  have h1 : ContinuousOn (chart φ.1 g) (invSet E a) := (φ.2 g).continuousOn
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val := by
    show Continuous fun y : GL (Fin a) (Cinf E) => (y : Matrix (Fin a) (Fin a) (Cinf E))
    exact Units.continuous_val
  have e : (fun y : GL (Fin a) (Cinf E) => φ.1 (g * infGL E a y)) = fun y => chart φ.1 g (toL y.val) :=
    funext fun y => (chart_val φ.1 g y).symm
  rw [e]
  exact h1.comp_continuous h2 fun y => val_mem_invSet y

theorem continuous_kavg [FirstCountableTopology (GL (Fin a) (Cinf E))] [LocallyCompactSpace (GL (Fin a) (Cinf E))]
    [MeasurableSpace (Kinf E a)] [BorelSpace (Kinf E a)] [CompactSpace (Kinf E a)]
    (ν : Measure (Kinf E a)) [IsFiniteMeasure ν] {F : GL (Fin a) (Cinf E) → ℂ} (hF : Continuous F) :
    Continuous (kavg ν F) := by
  have hc : Continuous (Function.uncurry fun (y : GL (Fin a) (Cinf E)) (k : Kinf E a) =>
      F (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹)) :=
    hF.comp (((continuous_toUnits_Kinf.comp continuous_snd).mul continuous_fst).mul
      (continuous_toUnits_Kinf.comp continuous_snd).inv)
  have := continuous_parametric_integral_of_continuous (μ := ν) hc (s := Set.univ) isCompact_univ
  show Continuous fun y => ∫ k, F (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) ∂ν
  simpa using this

theorem kavg_one [MeasurableSpace (Kinf E a)] (ν : Measure (Kinf E a)) [IsProbabilityMeasure ν]
    (F : GL (Fin a) (Cinf E) → ℂ) : kavg ν F 1 = F 1 := by
  simp [kavg]

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite →
    ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧
      HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g :=
  GlobalTheory.T.exists_harishChandra_reproducing_function_GLinfinity

end GlobalTheory.HCAlphaGL

end
