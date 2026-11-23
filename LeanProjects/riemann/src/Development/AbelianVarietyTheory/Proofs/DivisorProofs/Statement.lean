import Mathlib
import ReciprocityTheory.NeutralLocalFields.GrunwaldWang
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
import Formalism.ConjugateSelfDual.Statement

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CMTower

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def CMChain (v₀ : HeightOneSpectrum (𝓞 E)) (T T' : IntermediateField E Ω) : Prop :=
  ∃ (k : ℕ) (C : Fin (k + 1) → IntermediateField E Ω) (p : Fin k → ℕ) (hfd : ∀ i, FiniteDimensional E (C i)),
    C 0 = T ∧ C (Fin.last k) = T' ∧
    (∀ i, haveI := hfd i; haveI : NumberField (C i) := NumberField.of_module_finite E (C i); IsCMField (C i)) ∧
    (∀ i : Fin k, (p i).Prime ∧ ∃ h : C i.castSucc ≤ C i.succ,
      Module.finrank (C i.castSucc) (IntermediateField.extendScalars h) = p i ∧
      IsGalois (C i.castSucc) (IntermediateField.extendScalars h)) ∧
    ∀ i, haveI := hfd i; haveI : NumberField (C i) := NumberField.of_module_finite E (C i)
      ∀ v : HeightOneSpectrum (𝓞 (C i)), v.asIdeal.LiesOver v₀.asIdeal →
        v.asIdeal.ramificationIdx (𝓞 E) = Module.finrank E (C i)

def Statement : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (m : ℕ), 0 < m → ∀ (u ϖ : w.adicCompletion E), Valued.v u = 1 → Valued.v ϖ = WithZero.exp (-1) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), w ∉ S →
    ∃ (k : ℕ) (T : Fin (k + 1) → IntermediateField E Ω) (p : Fin k → ℕ)
      (hfd : ∀ i, FiniteDimensional E (T i)),
      T 0 = ⊥ ∧
      (∀ i, haveI := hfd i; haveI : NumberField (T i) := NumberField.of_module_finite E (T i); IsCMField (T i)) ∧
      (∀ i : Fin k, (p i).Prime ∧ ∃ h : T i.castSucc ≤ T i.succ,
        Module.finrank (T i.castSucc) (IntermediateField.extendScalars h) = p i ∧
        IsGalois (T i.castSucc) (IntermediateField.extendScalars h)) ∧
      (haveI := hfd (Fin.last k); haveI : NumberField (T (Fin.last k)) := NumberField.of_module_finite E _
      ∃ (w'' : HeightOneSpectrum (𝓞 (T (Fin.last k)))) (_ : IsPlaceOver A w'')
          (_ : w''.asIdeal.LiesOver w.asIdeal),
        normV w'' = normV w ^ m ∧ w''.asIdeal.ramificationIdx (𝓞 E) = normV w ^ m - 1 ∧
        ∃ y : w''.adicCompletion (T (Fin.last k)),
          y ^ (normV w ^ m - 1) = KStar.Choice.complMap w w'' (u * ϖ)) ∧
      ∃ v₀ : HeightOneSpectrum (𝓞 E), v₀ ∉ S ∧ v₀ ≠ w ∧ ∀ i,
        haveI := hfd i; haveI : NumberField (T i) := NumberField.of_module_finite E (T i)
        ∀ v : HeightOneSpectrum (𝓞 (T i)), v.asIdeal.LiesOver v₀.asIdeal →
          v.asIdeal.ramificationIdx (𝓞 E) = Module.finrank E (T i)

end GlobalTheory.CMTower
