import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem cuspForm_isSqInt_and_isDiscrete :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
      (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧
        ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  intro E _ _ _ a
  have hB : CuspFormsBoundedGL :=
    GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
      (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)
  have h1 : ∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1 :=
    fun φ hφ h' =>
      have hC := hB.of_invariant hφ h'
      GlobalTheory.DiscChar.isSqInt_of_bounded h' (C := hC.choose) hC.choose_spec
  exact ⟨h1, fun x hx => ⟨fun φ hφ => (x.cusp φ hφ).1, fun φ hφ => h1 φ (x.cusp φ hφ) (hx φ hφ), x.stable, x.ne_bot,
    x.irred⟩⟩

end GlobalTheory.ResW

end
