import Mathlib
import Formalism.PeriodIntegrals.ProdFormulaE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrBase

noncomputable section

open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.St

def HaarAlg : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [Module.Free K A] [Module.Finite K A] [IsModuleTopology K A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (y : A), IsUnit y → ∀ S : Set A,
      μ ((fun z => y * z) '' S) = ENNReal.ofReal (modF K (Algebra.norm K y)) * μ S

def NormLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ι : F →+* K), DenseRange ι →
    (∀ x y : F, (ι x ≤ᵥ ι y) ↔ p.valuation F x ≤ p.valuation F y) →
    ∀ z : F, modF K (ι z) = FinitePlace.mk p z

def TrInt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
    (w : K), IsIntegral ℤ w → ‖Algebra.trace ℚ_[ℓ] K w‖ ≤ 1

def ResCharIff : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (ℓ : ℕ), ℓ.Prime →
    (resChar p = ℓ ↔ ((ℓ : 𝓞 F) ∈ p.asIdeal))

end PI.ProdFormulaE.St

end
