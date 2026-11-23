import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.E.E3

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def Mult (S : Set (GA E N)) (n : ℕ) : Prop :=
  ∀ x : GA E N, {γ : (ratGL E N).range | (γ : GA E N) * x ∈ S}.encard ≤ n

def Loc (φ : GA E N → ℂ) : Prop :=
  letI : MeasurableSpace (GA E N) := borel _
  ∀ μ : Measure (GA E N), μ.IsHaarMeasure → ∃ (C : ℝ) (M : ℕ), ∀ S : Set (GA E N), IsCompact S → ∀ (n : ℕ) (R : ℝ), 0 ≤ R →
    Mult S n → (∀ g ∈ S, logSize g ≤ R) → ∫⁻ g in S, ‖φ g‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * n * (1 + R) ^ M)

def SizeT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (Q₁ Q₂ : Set (GA E N)), IsCompact Q₁ → IsCompact Q₂ →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ q₁ ∈ Q₁, ∀ q₂ ∈ Q₂, ∀ x : Fin N → ℝ, logSize (q₁ * An.tor E x * q₂) ≤ C * (1 + ‖x‖)

def MultC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (Q : Set (GA E N)), IsCompact Q →
  ∃ n : ℕ, ∀ z : GA E N, (∀ g, z * g = g * z) → Mult ((fun q => z * q) '' Q) n

def InterpolationL2Bound : Prop := ∀ (X Y : Type) [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (ν : Measure Y) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (F : X → Y → ℂ),
  (∀ x, Continuous (F x)) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range F)) →
  ∃ Ω : Set Y, IsCompact Ω ∧ ∀ y₀, ∃ C : NNReal, ∀ x, ‖F x y₀‖ₑ ^ 2 ≤ C * ∫⁻ y in Ω, ‖F x y‖ₑ ^ 2 ∂ν

def FinType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (m : (E →+* ℂ) → Multiset ℂ) (S : Set (Sm E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W →
  (∀ φ ∈ S, IsAutForm φ ∧ (∀ u ∈ K, ∀ x, φ.1 (x * finGL E N u) = φ.1 x) ∧
    ∀ x, (fun k : Kinf E N => φ.1 (x * infGL E N (Unitary.toUnits k))) ∈ W) →
  (∀ τ, HasInfCharGL (Submodule.span ℂ S) τ (m τ)) → FiniteDimensional ℂ (Submodule.span ℂ S)

def LocSl : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (M : ℕ) (F : H E a b → ℂ), Continuous F →
  LeftInv (fun _ : Unit => F) → WL2 D M (fun _ : Unit => F) →
  (FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun x y => F (x, y))) → ∀ y, Loc fun x => F (x, y)) ∧
  (FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y x => F (x, y))) → ∀ x, Loc fun y => F (x, y))

def LocNonPos : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (φ : Sm E N), IsAutForm φ → Loc φ.1 →
  ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c ≤ 0

def CentEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (m : (E →+* ℂ) → Multiset ℂ),
  (∀ τ, HasInfCharGL V τ (m τ)) →
  ∃ z : ℂ, ∀ φ ∈ V, ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = Complex.exp (z * t) * φ.1 g

def CentRe : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (φ : GA E N → ℂ) (z : ℂ), Continuous φ → φ ≠ 0 → Loc φ →
  (∀ (t : ℝ) g, φ (splitCentre E N t * g) = Complex.exp (z * t) * φ g) → z.re = 0

def HullAut : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (S : Set (Sm E N)), (∀ φ ∈ S, IsAutForm φ) →
  (∀ φ ∈ hull S, IsAutForm φ) ∧ ∀ τ m, HasInfCharGL (Submodule.span ℂ S) τ m → HasInfCharGL (hull S) τ m

def HullNonPos : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (S : Set (Sm E N)),
  (∀ φ ∈ S, IsAutForm φ ∧ ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c ≤ 0) → SpectralAccumulation.NonPos (hull S)

def PairSp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (F : H E a b → ℂ) (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)),
  (∀ y, ∃ φ ∈ U₁, φ.1 = fun x => F (x, y)) → (∀ x, ∃ ψ ∈ U₂, ψ.1 = fun y => F (x, y)) →
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y x => F (x, y))) → F ∈ SpectralAccumulation.pairSpace U₁ U₂

def LocSlGlue : Prop := SizeT → MultC → InterpolationL2Bound → LocSl
def LocNonPosGlue : Prop := SizeT → LocNonPos
def CentReGlue : Prop := SizeT → MultC → CentRe
def Asm : Prop := FinType → LocSl → LocNonPos → CentEig → CentRe → HullAut → HullNonPos → PairSp → E3

end PositivityTheory.Rg.BcB.E.E3

end
