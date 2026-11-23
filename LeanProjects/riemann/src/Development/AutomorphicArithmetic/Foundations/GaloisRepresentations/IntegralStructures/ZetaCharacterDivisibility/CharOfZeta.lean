import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Div

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev cj : Ideles E →* Ideles E := Units.map (conjAd E).toMonoidHom

def quo : Ideles E →* Ideles E := (MonoidHom.id (Ideles E)) / cj E

theorem quo_apply (z : Ideles E) : quo E z = z / cj E z := rfl

def IsZeta (a : ℕ) (ζ : Ideles E →* UA E a) : Prop :=
  ∀ z, ((ζ z : UA E a) : GA E a) = Matrix.GeneralLinearGroup.scalar (Fin a) (quo E z)

def ZetaEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), ∃ ζ : Ideles E →* UA E a, IsZeta E a ζ ∧ Continuous ζ ∧
    (∀ z x, ζ z * x = x * ζ z) ∧ (∀ k : Eˣ, ζ (diagUnits E k) ∈ ratU E a) ∧ ∀ z, cj E z = z → ζ z = 1

def ZetaLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ζ : Ideles E →* UA E a), IsZeta E a ζ →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ u : (w.adicCompletion E)ˣ,
      ζ (localIdele E w u) ∈ locU a w ∧ cLoc w (ζ (localIdele E w u)) = Matrix.GeneralLinearGroup.scalar (Fin a) u

def SchurU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ z : UA E a, (∀ x, z * x = x * z) → ∃ c : ℂ, ∀ φ ∈ U, RU E a z φ = c • φ

def CharOfZeta : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ ζ : Ideles E →* UA E a, Continuous ζ → (∀ z x, ζ z * x = x * ζ z) → (∀ k : Eˣ, ζ (diagUnits E k) ∈ ratU E a) →
    (∀ z, ∃ c : ℂ, ∀ φ ∈ U, RU E a (ζ z) φ = c • φ) →
    ∃ χ : HChar E, ∀ z, ∀ φ ∈ U, RU E a (ζ z) φ = ((χ.1 z : ℂˣ) : ℂ) • φ

def AlgOfFix : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E), (∀ z, cj E z = z → χ.1 z = 1) →
    ∃ n : (E →+* ℂ) → ℤ, IsAlgPos χ n

def SatCent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ x : σ.V, x ≠ 0 ∧
      (∀ u : (w.adicCompletion E)ˣ, IsUnitAt w u → σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x = x) ∧
      ∀ u : (w.adicCompletion E)ˣ, IsUnifAt w u →
        σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin a) u) x = ((B.prod : ℂˣ) : ℂ) • x

end UpperTheory.Gal.Int.Div

end
