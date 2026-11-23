import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.CuspBridge

theorem unipGL_eq_unip {R : Type} [CommRing R] {a r : ℕ} (X : AutomorphicForm.UPos a r → R) :
    AutomorphicForm.unipGL X = unip X := by
  apply Units.ext
  rfl

theorem isAddHaarMeasure_unipMeasure (E : Type) [Field E] [NumberField E] (a r : ℕ) :
    (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem isCuspidal_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → AutomorphicForm.IsCuspidal φ.1 := by
  intro E _ _ _ a φ h r h0 h1 g
  have h2 := h.2 r h0 h1 (AutomorphicForm.unipMeasure E a r) (AutomorphicForm.unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure E a r) AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain g
  simpa only [AutomorphicForm.constantTerm, unipGL_eq_unip] using h2

end GlobalTheory.CompanionTheory.CuspBridge

end
