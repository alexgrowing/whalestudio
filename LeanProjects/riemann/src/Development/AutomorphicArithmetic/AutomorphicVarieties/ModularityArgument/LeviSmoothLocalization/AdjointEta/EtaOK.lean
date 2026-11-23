import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lin3 (ν c : kˣ →* ℂˣ) : ℂ[X] := lin (ν * c) * lin c * lin (ν⁻¹ * c)

def Ram3 (ν c : kˣ →* ℂˣ) : Prop := ¬ IsUnram (ν * c) ∧ ¬ IsUnram c ∧ ¬ IsUnram (ν⁻¹ * c)

end Loc

def tri (a x : ℂˣ) : Multiset ℂ := (({a * x, x, a⁻¹ * x} : Multiset ℂˣ)).map fun b : ℂˣ => (b : ℂ)

def par (D : Ad3.Dat) (χ : HChar ℚ) (p : Ad3.Pl) : Multiset ℂ := tri (D.ν p (unif (p.adicCompletion ℚ))) (χ.val p)

def arch (k : ℕ) (s : ℂ) : ℂ := Ad3.lR k true s * Ad3.lR k false s

structure EtaOK (K : Type) [Field K] [NumberField K] (η : HeckeCharacter ℚ) : Prop where
  fin : IsOfFinOrder η
  sgn : ∀ w : InfinitePlace ℚ, ((η.infiniteComponent w (-1) : Circle) : ℂ) = -1
  ae : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, (toH η).UnrAt v ∧ ∀ w : PlacesOver K v,
    IsPrimitiveRoot ((toH η).val v) (fdeg w) ∧ Fintype.card (PlacesOver K v) * fdeg w = 2
  loc : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (w : PlacesOver K v), ((toH η).loc v).comp (nm w) = 1 ∧
    (∀ (w' : PlacesOver K v) (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ), IsUnram (θ.comp (nm w)) → IsUnram (θ.comp (nm w'))) ∧
    ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ → IsSmoothChar (θ.comp (nm w)) ∧ (IsUnram θ → IsUnram (θ.comp (nm w))) ∧
      (IsUnram (θ.comp (nm w)) → ((Finset.range 2).filter fun j => IsUnram (θ * ((toH η) ^ j).loc v)).card =
        ∑ w' : PlacesOver K v, fdeg w')

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
