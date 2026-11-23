import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified

noncomputable section

namespace UpperTheory.GalN

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At UpperTheory.Lit.Car

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def LGCatN {i : N.Loc} (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) (A : NAut N) (w : PlE H) : Prop :=
  ∀ x, ∃ P, A.ptV i P = some x ∧
    RelW N A (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w) (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2))

variable (A : NAut N)

def AwayRepN (i : N.Loc) (m : ℕ) (L : ∀ w, A.LP w) : Prop :=
  ∃ r : G H.E N.Om →* GL (Fin m) (Qbar (N.l i)), ContQ N i r ∧ IsSSRep r ∧
    ∀ w, w ∉ placesOver H.E (N.l i) → RelW N A (A.wdOf i r w) (L w)

def GalIsoN (i : N.Loc) : Prop := ∀ (P : A.AV i) (Pa : List (Part A.CG)), IsBCV N A i P Pa →
  ∃ r : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i)),
    Continuous (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))) ∧
    IsSSRep r ∧ ∀ w, w ∉ placesOver H.E (N.l i) →
      RelW N A (A.wdOf i r w) (A.lpTw (isoLoc N A Pa w) ((1 - (R.nV : ℝ)) / 2))
end

def LGCN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w : PlE D.host, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → LGCatN D.nd r D.naut w

def LgcGN (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → LGCatN D.nd r D.naut w

def RowRepAtGN (D : D7) : Prop := ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
  ∃ (Sig : List (Part D.naut.CG)) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
    HasParamW D.nd D.naut i σ Sig ∧ IsRepOfSig D.nd D.naut i Sig ρ ∧
    ∀ k v, D.nd.l i ≠ D.host.g k →
      RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v))
        (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2))

def IsoRepN (D : D7) : Prop := ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), IsBCV D.nd D.naut i P Pa →
  ∃ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) ∧
    ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧
      RelA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ

end UpperTheory.GalN
