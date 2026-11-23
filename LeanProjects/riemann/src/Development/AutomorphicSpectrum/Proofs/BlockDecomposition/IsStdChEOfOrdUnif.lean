import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite
import GroundTheory.LocalFields.LocalFourierTrace
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.UnramifiedDefs

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta

theorem isStd_chE_of_ord_unif : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ χ : AddChar F Circle, Ad3.IsStd χ → Ad3.IsStd (Ad3.K.GL2LocalData.chE E χ) := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ hord χ hχ
  obtain ⟨hc, h1, h0⟩ := hχ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have he : ramificationIndex F E = 1 := by
    have h := ord_algebraMap (K := F) (L := E) (unifUnit F : F)
    rw [hord, ord_unifUnit] at h
    omega
  haveI : IsUnramified F E := ⟨he⟩
  have hd : differentExponent F E = 0 := (differentExponent_eq_zero_iff F E).2 inferInstance
  refine ⟨continuous_traceChar hc h1, traceChar_ne_one hc h1, ?_⟩
  have := addCharConductor_traceChar_of_eq_zero (L := E) hc h1 h0
  rw [hd] at this
  have h2 : addCharConductor (traceChar E χ) = 0 := by simpa using this
  exact h2

end GlobalTheory.CompanionTheory.SphTheta
