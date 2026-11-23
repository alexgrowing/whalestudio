import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraUniformSmoothingTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsFixedLevelKtypesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsSpanLevelStatement

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

namespace GlobalTheory.HCFGL

theorem finiteDimensional_single (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ih : ∀ b < a, ∀ L : Subgroup (GL (Fin b) (Af E)), IsOpen (L : Set (GL (Fin b) (Af E))) →
      ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite →
      ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E b L W X N)))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) :
    FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W {χ} N)) := by
  obtain ⟨n, T, hT⟩ := GlobalTheory.T.finiteDimensional_forms_span_level E a ih L hL W hW χ N
  obtain ⟨α, hα, hrep⟩ := GlobalTheory.T.harishChandra_uniform_smoothing_test_function E a L hL W hW χ N (MeasureTheory.Measure.addHaar) inferInstance
  have hQ := GlobalTheory.T.finiteDimensional_cuspForms_fixedLevel_Ktypes E a L hL W hW χ N MeasureTheory.Measure.addHaar inferInstance α hα hrep
  set P := Submodule.span ℂ (formsGL E a L W {χ} N)
  set Q := Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}
  have h1 : (P.map T).FG := IsNoetherian.noetherian _
  have h2 : (P ⊓ LinearMap.ker T).FG := by
    have hle : P ⊓ LinearMap.ker T ≤ Q := by
      intro φ hφ
      have hS := GlobalTheory.T.harishChandraFiniteFormsGL_single_char_span_mem E a L W χ N φ hφ.1
      exact Submodule.subset_span ⟨hS, hT φ hS hφ.2⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_of_fg_inf_ker T h1 h2)

theorem coreFiniteGL : CoreFiniteGL := by
  intro E _ _ _ a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro L hL W hW X hX N
  have hle : Submodule.span ℂ (formsGL E a L W X N) ≤
      hX.toFinset.sup fun χ => Submodule.span ℂ (formsGL E a L W {χ} N) := by
    rw [Submodule.span_le]
    rintro φ ⟨h1, h2, h3, χ, hχ, h4⟩
    have hmem : Submodule.span ℂ (formsGL E a L W {χ} N) ≤
        hX.toFinset.sup fun χ => Submodule.span ℂ (formsGL E a L W {χ} N) :=
      Finset.le_sup (f := fun χ => Submodule.span ℂ (formsGL E a L W {χ} N)) (hX.mem_toFinset.2 hχ)
    exact hmem (Submodule.subset_span ⟨h1, h2, h3, χ, rfl, h4⟩)
  have hs : ∀ χ, FiniteDimensional ℂ (Submodule.span ℂ (formsGL E a L W {χ} N)) := fun χ =>
    finiteDimensional_single E a (fun b hb => ih b hb) L hL W hW χ N
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.HCFGL
