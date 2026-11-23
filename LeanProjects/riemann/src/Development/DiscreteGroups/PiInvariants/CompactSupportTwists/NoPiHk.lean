import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Module.End ℂ (Sm E n) :=
  finRep E n (locGL E n w g)

def piZ (π : CuspSub E n) (z : ℂ) : Set (Sm E n) :=
  {f | ∃ ψ ∈ π.V, ∀ g, f.1 g = ψ.1 g * Complex.exp (z * logAbs g.val.det)}

def FixAt (w : HeightOneSpectrum (𝓞 E)) (f : Sm E n) : Prop := ∀ k ∈ GlobalTheory.LFun.KGL w n, locT w k f = f

def InKgK (w : HeightOneSpectrum (𝓞 E)) (g y : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∃ k₁ ∈ GlobalTheory.LFun.KGL w n, ∃ k₂ ∈ GlobalTheory.LFun.KGL w n, y = k₁ * g * k₂

def IsHk (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) :
    Prop :=
  (∀ r ∈ R, InKgK w g r) ∧ ∀ y, InKgK w g y → ∃! r, r ∈ R ∧ r⁻¹ * y ∈ GlobalTheory.LFun.KGL w n

def hk (w : HeightOneSpectrum (𝓞 E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) : Module.End ℂ (Sm E n) :=
  ∑ r ∈ R, locT w r

def GenEig (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E n) (z : ℂ) (φ : Sm E n) : Prop :=
  ∀ w, w ∉ S → FixAt w φ ∧ (∃ v ∈ piZ π z, v ≠ 0 ∧ FixAt w v) ∧
    ∀ g R, IsHk w g R → ∃ (c : ℂ) (m : ℕ), (∀ v ∈ piZ π z, FixAt w v → hk w R v = c • v) ∧
      ((hk w R - c • (1 : Module.End ℂ (Sm E n))) ^ m) φ = 0

def InPiSpan (π : CuspSub E n) (φ : Sm E n) : Prop :=
  ∃ (k : ℕ) (ψ : Fin k → Sm E n) (f : Fin k → ℝ → ℂ), (∀ j, ψ j ∈ π.V ∧ Continuous (f j)) ∧
    ∀ g, φ.1 g = ∑ j, (ψ j).1 g * f j (logAbs g.val.det)

end Defs

def HeckeFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (z : ℂ)
  (U : Submodule ℂ (Sm E n)), IsStable U → (∀ φ ∈ U, IsAutForm φ) → ∀ φ ∈ U,
  ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (V₀ : Submodule ℂ (Sm E n)), FiniteDimensional ℂ V₀ ∧ V₀ ≤ U ∧ φ ∈ V₀ ∧
    (∀ w, w ∉ S → ∀ f ∈ V₀, FixAt w f) ∧
    (∀ w, w ∉ S → ∀ g R, IsHk w g R → ∀ f ∈ V₀, hk w R f ∈ V₀) ∧
    (∀ w, w ∉ S → ∀ w', w' ∉ S → ∀ g g' R R', IsHk w g R → IsHk w' g' R' →
      ∀ f ∈ V₀, hk w R (hk w' R' f) = hk w' R' (hk w R f)) ∧
    (∀ w, w ∉ S → ∃ v ∈ piZ π z, v ≠ 0 ∧ FixAt w v) ∧
    (∀ w, w ∉ S → ∀ g R, IsHk w g R → ∃ c : ℂ, ∀ v ∈ piZ π z, FixAt w v → hk w R v = c • v)

def EigSplit : Prop := ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (V₀ : Submodule ℂ V), FiniteDimensional ℂ V₀ →
  ∀ (ι : Type) (A : ι → Module.End ℂ V) (c : ι → ℂ) (T : V →ₗ[ℂ] V),
    (∀ i, ∀ f ∈ V₀, A i f ∈ V₀) → (∀ i j, ∀ f ∈ V₀, A i (A j f) = A j (A i f)) →
    (∀ i, ∀ f ∈ V₀, T (A i f) = A i (T f)) → (∀ i, ∀ f ∈ V₀, A i (T f) = c i • T f) →
    ∀ φ ∈ V₀, T φ ≠ 0 → ∃ φ₁ ∈ V₀, T φ₁ ≠ 0 ∧ ∀ i, ∃ m : ℕ, ((A i - c i • (1 : Module.End ℂ V)) ^ m) φ₁ = 0

def HeckeProj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
  (U : Submodule ℂ (Sm E n)), IsStable U → (∀ φ ∈ U, IsAutForm φ) → ∀ (z : ℂ) (T : Sm E n →ₗ[ℂ] Sm E n),
  (∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) → (∀ φ ∈ U, T φ ∈ piZ π z) →
    ∀ φ ∈ U, T φ ≠ 0 → ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (φ₁ : Sm E n), φ₁ ∈ U ∧ T φ₁ ≠ 0 ∧ GenEig S π z φ₁

def CTZero : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
  (S : Finset (HeightOneSpectrum (𝓞 E))) (z : ℂ) (φ : Sm E n), IsAutForm φ → GenEig S π z φ → IsCuspidal φ.1

def RCTZero : Prop := GlobalTheory.Published.JacquetShalikaRigidity → CTZero

def CuspEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n)
  (S : Finset (HeightOneSpectrum (𝓞 E))) (z : ℂ) (φ : Sm E n), IsCuspForm φ → GenEig S π z φ → InPiSpan π φ

def RCuspEig : Prop := GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.CuspidalMultiplicityOne → CuspEig

def SpanOrth : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ φ : Sm E n, InPiSpan π φ → Orth D π φ → φ = 0

end DiscreteGroups.T1.G

end
