import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DatEx (X : Stages) (f : Top.Fr X.B.toPre) (T : Top.TwDat X.B) : Prop :=
  ∀ (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok), I.Ok → I.C = f → Set.range I.xi = T.set f → SelHalf I →
    GrpAt X I → VolTieG X.toD7 → ∀ Wt : Set X.B.places.Pl, Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) →
      ∃ z : Dat X I hX T Wt, z.R.toRealDat.ExAt ∧ (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.Ok3 1 ∧ GlobalTheory.RealGeo.InGeo z.geo

def CoreAt (X : Stages) (f : Top.Fr X.B.toPre) : Prop :=
  ∃ (C : Formalism.L2.Pj.CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL),
    (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧
    (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧
    (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧
    (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧
    Formalism.L2.Pj.LawsJ C ∧ Formalism.L2.Pj.LawsCore C.toCore ∧ Formalism.IndefR.FWT.AlgTie C ∧
    C.pb = (Top.Fr.at X f).P.pb ∧ Formalism.L2.Host.ValLL X.toD7 (Top.Fr.at X f) ∧
    ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Top.Fr.at X f →
      ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y)

end GlobalTheory.Mem.R3

end
