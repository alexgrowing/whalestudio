import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue

noncomputable section

open NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

def ExpDec {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (r : ℕ) (F : GA E N → ℂ) : Prop :=
  ∃ (C : Finset ℂ) (G : ℂ → GA E N → ℂ), F = ∑ c ∈ C, G c ∧
    ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E N r t * g) = Complex.exp (c * t) * G c g

def NoLog : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N r : ℕ) (ψ : Sm E N), IsAutForm ψ →
  (∀ (t : ℝ) g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
  (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup) → 0 < r → r < N →
  ExpDec r (An.ctn r ψ.1)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
