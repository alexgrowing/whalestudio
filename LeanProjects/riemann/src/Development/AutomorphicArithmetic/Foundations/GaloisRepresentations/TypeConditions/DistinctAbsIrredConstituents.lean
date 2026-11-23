import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def DistinctAbsIrredConstituents (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : Algebra (Kf N i) K') (_ : FiniteDimensional (Kf N i) K'),
    ∀ x, (∀ W, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W →
        AbsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W) ∧
      ∀ W₁ W₂, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ →
        IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₂ →
        W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ W₂

def G3a (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ((N.l i ≠ H.g 0 ∧ N.l i ≠ H.g 1) ∨ GlobalTheory.CoefDuty.Live N i) → DistinctAbsIrredConstituents N i r

def ResidualCharpolyIndependent (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ (x y : N.X i) (g : G H.E N.Om),
    ((redRep N i (r x) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      ((redRep N i (r y) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly

def G3 (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop := G3a N i r ∧ ResidualCharpolyIndependent N i r

variable {N}
theorem g3 {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : At.G3 N i r) : G3 N i r := ⟨fun _ => h.1, h.2⟩
theorem g3' {i : N.Loc} {r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))} (h : G3 N i r) : G3 N i r := h
end

def DeRhamJumpsDistinctCondition (D : D7) : Prop :=
  (∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x,
      D.naut.IsdRW i (AdmissibleParameterJ.rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (AdmissibleParameterJ.rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀) ∧
  ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r

end UpperTheory.GalS
