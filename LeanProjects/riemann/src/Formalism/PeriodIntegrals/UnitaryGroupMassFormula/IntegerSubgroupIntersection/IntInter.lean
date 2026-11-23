import Mathlib
import Formalism.PeriodIntegrals.GaugeGap

noncomputable section

namespace PI.GaugeCharW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def InfFun : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ L : Ainf F →+ ℝ, Continuous L ∧
    (∀ a : 𝓞 F, ∃ n : ℤ, L (algebraMap F (Ainf F) (a : F)) = n) ∧ ∃ t, L t = 1 / 2

def IntInter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : F),
    (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) a v ∈ v.adicCompletionIntegers F) →
    ∃ b : 𝓞 F, (b : F) = a

def OpenInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {y : Af F | ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F}

def ExtChar : Prop :=
  ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (K U : AddSubgroup G), IsOpen (U : Set G) →
    ∀ g : G →+ AddCircle (1 : ℝ), Continuous g → (∀ x ∈ K, x ∈ U → g x = 0) →
    ∃ h : G →+ AddCircle (1 : ℝ), Continuous h ∧ (∀ x ∈ K, h x = 0) ∧ ∀ x ∈ U, h x = g x

end PI.GaugeCharW
