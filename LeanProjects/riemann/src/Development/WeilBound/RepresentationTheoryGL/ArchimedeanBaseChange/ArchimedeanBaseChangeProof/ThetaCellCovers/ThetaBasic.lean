import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele)
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

def admitted (t₀ : ℝ) (x : Fin n → ℝ) : Prop := ∀ r, -t₀ ≤ An.sr x r

def sieg (ω : Set (GA E n)) (t₀ : ℝ) : Set (GA E n) :=
  {g | ∃ b ∈ ω, ∃ x : Fin n → ℝ, admitted t₀ x ∧ ∃ k ∈ maxCompact (K := E) (n := n), g = b * An.tor E x * k}

def red (g : GA E n) : ℝ := ⨅ γ : GL (Fin n) E, logSize (ratGL E n γ * g)

def Om (ω : Set (GA E n)) : Prop := IsCompact ω ∧ ω ⊆ (adelicBorel (K := E) (n := n) : Set _)

def RatProper : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
  Function.Injective (ratGL E n) ∧ Countable (GL (Fin n) E) ∧
    ∀ C : Set (GA E n), IsCompact C → {γ : GL (Fin n) E | ratGL E n γ ∈ C}.Finite

def ThetaBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  Continuous (thetaA E n) ∧ (∀ g, thetaA E n (thetaA E n g) = g) ∧
    ∀ γ, thetaA E n (ratGL E n γ) = ratGL E n (thetaE E n γ)

def Cover : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
  ∃ (ω : Set (GA E n)) (t₀ : ℝ), Om ω ∧ 0 ≤ t₀ ∧ ∀ g : GA E n, ∃ γ, ratGL E n γ * g ∈ sieg ω t₀

def AdmLe : Prop := ∀ (n : ℕ) (t₀ : ℝ) (x : Fin n → ℝ), 0 ≤ t₀ → admitted t₀ x → ∀ i j : Fin n, i ≤ j → x j ≤ x i + n * t₀

def ConjCpt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (ω : Set (GA E n)) (t₀ : ℝ),
  Om ω → 0 ≤ t₀ → ∃ ω' : Set (GA E n), IsCompact ω' ∧ ∀ b ∈ ω, ∀ x, admitted t₀ x → (An.tor E x : GA E n)⁻¹ * b * An.tor E x ∈ ω'

def CellCover : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
  ∃ Ω₀ : Set (GA E n), IsCompact Ω₀ ∧ ∀ g : GA E n, ∃ (γ : GL (Fin n) E) (m : Fin n → ℤ), ∃ o ∈ Ω₀,
    ratGL E n γ * g = An.tor E (fun i => (m i : ℝ)) * o

def LatSum : Prop := ∀ n M : ℕ, 2 * n ≤ M →
  ∑' m : Fin n → ℤ, ENNReal.ofReal ((1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ))) ≠ ⊤

def TorNorm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E],
  (∀ t : ℝ, logAbs ((posIdele (K := E) (Real.exp t) (Real.exp_pos t) : (Ad E)ˣ) : Ad E) = Module.finrank ℚ E * t) ∧
  ∀ (n : ℕ) (x : Fin n → ℝ), logAbs (An.tor E x : GA E n).val.det = Module.finrank ℚ E * ∑ i, x i ∧
    logSize (An.tor E x : GA E n) ≤ 2 * Module.finrank ℚ E * ‖x‖

def DegCell : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (Ω₀ : Set (GA E n)),
  IsCompact Ω₀ → ∃ C : ℝ, ∀ x : Fin n → ℝ, ∀ o ∈ Ω₀,
    (∀ i : Fin n, |deg (An.tor E x * o : GA E n) (Submodule.span E {Pi.single i 1}) - Module.finrank ℚ E * x i| ≤ C) ∧
    |deg (An.tor E x * o : GA E n) ⊤ - Module.finrank ℚ E * ∑ i, x i| ≤ C

def DegRight : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
  ∀ (x h : GA E n) (W : Submodule E (Fin n → E)), deg (x * h) W ≤ deg x W + C * (1 + logSize h)

def CutBox : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (Ω₀ : Set (GA E n)),
  IsCompact Ω₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin n → ℝ, ∀ o ∈ Ω₀, ∀ σ : ℝ, 0 ≤ σ →
    (∀ W : Submodule E (Fin n → E), Module.finrank E W = 1 → deg (An.tor E x * o : GA E n) W ≤ σ) →
    -σ ≤ deg (An.tor E x * o : GA E n) ⊤ → ‖x‖ ≤ C * (1 + σ)

def RedBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
  (∀ γ (g : GA E n), red (ratGL E n γ * g) = red g) ∧ (∀ g : GA E n, 0 ≤ red g ∧ red g ≤ logSize g) ∧
    @Measurable _ _ (borel (GA E n)) _ red

def SizeCont : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
  Continuous (logSize : GA E n → ℝ)

def RedCell : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Ω₀ : Set (GA E n)),
  IsCompact Ω₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin n → ℝ, ∀ o ∈ Ω₀,
    ‖x‖ ≤ C * (1 + red (An.tor E x * o : GA E n)) ∧ red (An.tor E x * o : GA E n) ≤ C * (1 + ‖x‖)

def CutRed : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
  ∀ τ : ℝ, 0 ≤ τ → ∀ g ∈ cutSet E n τ, red g ≤ C * (1 + τ)

def DomEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) [MeasurableSpace (GA E n)]
  [BorelSpace (GA E n)] (μ : Measure (GA E n)), ∃ F, IsFundamentalDomain (ratGL E n).range F μ

end PositivityTheory.Rg.BcB.E1

end
