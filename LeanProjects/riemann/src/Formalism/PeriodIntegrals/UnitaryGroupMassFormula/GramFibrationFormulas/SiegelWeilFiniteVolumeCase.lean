import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.LocalInductionFinitePlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.AdelicVectorDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.WeilRepresentationIrreducible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.SL2AdelicReductionTheory

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def FinVolAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVolH σ J

def SiegelWeilFibrationFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1a1 F E σ M J

def TgtSW1a2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1a2 F E σ M J

def TgtSW1b1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b1 F E σ M J

def TgtSW1b2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1b2 F E σ M J

def TgtSW1c1 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1c1 F E σ M J

def SiegelWeilVolumeFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Formalism.MainNotions.StandardLattice.SW1c3 F E σ M J

def IsDxDq0 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ν {X | ¬ (qR (AF F) σ J (X 0) = 0 ∧ FreeT (F := F) (E := E) (Ainf F) (projInf X) ∧
    (∀ v, FreeT (F := F) (E := E) (Fv F v) (projV v (projFin X))) ∧
    ∀ᶠ v in Filter.cofinite, projV v (projFin X) 0 ∈ X0int b σ J v)} = 0 ∧
  ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
    (μv : ∀ v, Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (Fv F v)),
    SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual νi (fun s t => psiInf F ψ (s * t)) →
    (∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) →
    (∀ v, SelfDual (νv v) (fun s t => psiV F ψ v (s * t))) →
  ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
    (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
    IsQFibInf σ J μi νi fi → (∀ v, IsQFib σ J v (μv v) (νv v) (fv v)) →
  ∀ Φ Φi Φv, IsPureL b Φ Φi Φv →
    ∫⁻ X, Φ X ∂ν = (∫⁻ X, Φi X ∂(fi 0)) * ∏' v, ∫⁻ X, Φv v X ∂(fv v 0)

def NullVectorSumFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    3 ≤ M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E), IsDxDq0 b σ J ψ ν →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
    ∀ Ψ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Ψ →
      meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = 0},
        Ψ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))) = ∫⁻ y, Ψ y ∂ν

def SiegelWeilFiniteVolumeCase : Prop := FinVolAll → RationalPointsLattice → IsotropicLatticeCount → SiegelWeilFibrationFormula ∧ TgtSW1a2

def SiegelWeilDensityCase : Prop :=
  FinVolAll → RationalPointsLattice → SelfDualMeasuresExist → FiniteFibreMeasureFormula → ArchimedeanFibreFamily → GlobalDensityProductFormula → HermitianDilationFormula → NullVectorSumFormula → AnisotropicOrbitSurjective → UnitaryStabilizerQuotient →
    TgtSW1b1 ∧ TgtSW1b2 ∧ SiegelWeilVolumeFormula

def SiegelWeilPureFormCase : Prop :=
  FinVolAll → RationalPointsLattice → SelfDualMeasuresExist → GramMapFibreFamily → ArchimedeanGramFibreFamily → SiegelWeilPureFormula → SchwartzBruhatConvergence → TgtSW1c1

def SiegelWeilGlobalInduction : Prop :=
  FinVolAll → RationalPointsLattice → SelfDualMeasuresExist → GramMapFibreFamily → GramFibreFamilyUnique → HaarScalingGramMap → ArchimedeanGramFibreFamily → ArchimedeanHaarScaling → WittTransitivityFreeFrames → GoodPlaceOrthonormalLattice →
    AnisotropicOrbitSurjective → UnitaryStabilizerQuotient → OrbitUnfoldingFormula → FiniteFibreMeasureFormula → ArchimedeanFibreFamily → GlobalDensityProductFormula → HermitianDilationFormula → HermitianDiagonalization → LocalInductionFinitePlace → SiegelWeilPureFormula

end PI.GramFibrationFormulas
