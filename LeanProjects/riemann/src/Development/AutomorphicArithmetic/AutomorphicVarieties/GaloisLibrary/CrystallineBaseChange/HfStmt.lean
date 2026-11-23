import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis
open scoped Matrix

namespace UpperTheory.V.Br

def IsRot {F : Type} [Field F] (θ : TR.Rinf F) (h : GL (Fin 2) (TR.Rinf F)) : Prop :=
  (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) =
    !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]

def RotEig : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : TR.Sm F 2) (z : ℂ), (∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) →
    ∀ θ h, IsRot θ h → ∀ g, φ.1 (g * TR.infGL F 2 h) = Complex.exp (z * ∑ v, (θ v : ℂ)) * φ.1 g

structure Moves {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : ℕ) (Z : Set (GA F 2)) : Prop where
  unip : ∀ (x : Ad F), ∀ g ∈ Z, aff 1 x * g ∈ Z
  rat : ∀ (a : Fˣ), ∀ g ∈ Z, aff (diagUnits F a) 0 * g ∈ Z
  pos : ∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ∀ g ∈ Z, TR.infGL F 2 (aff y 0) * g ∈ Z
  cent : ∀ (z : Ideles F), ∀ g ∈ Z, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ Z
  lev : ∀ u ∈ KLev F 2 M, ∀ g ∈ Z, g * finGL F 2 u ∈ Z
  rot : ∀ θ h, IsRot θ h → ∀ g ∈ Z, g * TR.infGL F 2 h ∈ Z

def IwasawaA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : GA F 2), ∃ (z y : Ideles F) (x : Ad F) (r : TR.Kinf F 2),
    ∃ u ∈ KLev F 2 1, g = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y x * (TR.infGL F 2 (Unitary.toUnits r) * finGL F 2 u)

def CuspSet : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℕ), 1 ≤ M → ∃ S : Set (GA F 2), S.Finite ∧
    ∀ Z : Set (GA F 2), S ⊆ Z → Moves M Z → Z = Set.univ

def CtMoves : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F))
    [μ.IsAddHaarMeasure] (D : Set (NA F)), IsAddFundamentalDomain (ratN F 2 1) D μ → ∀ (k : ℕ) (c : Pl F → ℕ) (ω : HChar F),
    IsOfFinOrder ω → ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ M : ℕ, (∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ) →
    Moves M {g | cterm μ D φ.1 g = 0}

def CtOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∃ (_ : MeasurableSpace (NA F)) (_ : BorelSpace (NA F)) (μ : Measure (NA F))
    (_ : μ.IsAddHaarMeasure) (D : Set (NA F)), IsAddFundamentalDomain (ratN F 2 1) D μ ∧
    ∀ φ : GA F 2 → ℂ, (∀ γ g, φ (ratGL F 2 γ * g) = φ g) → (∀ g, cterm μ D φ g = 0) → IsCuspidal φ

def HolCuspFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : HChar F, IsOfFinOrder ω →
    (∃ M : ℕ, 1 ≤ M ∧ ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ) ∧
    FiniteDimensional ℂ (Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ ∧ TR.IsCuspForm φ})

end UpperTheory.V.Br
