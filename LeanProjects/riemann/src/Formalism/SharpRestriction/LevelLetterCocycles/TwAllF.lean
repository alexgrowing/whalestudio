import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
import Formalism.SharpRestriction.SmoothDesignExistence.EvSplit
import Formalism.SharpRestriction.LevelLetterCocycles.TwQDist

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def GoodTwFAll {eps : ℝ} (Fm : FamP eps) : Prop :=
  Formalism.MainNotions.Pk.EvL Fm fun x hx i => ∃ I : TwIn (Fm.D x i), I.E = twE Fm x hx i ∧
            ∃ (Q : (Fm.D x i).what₂.places.Pl → Finset (PlE (Fm.D x i).host)) (k' : (Fm.D x i).what₂.places.Pl → ℕ)
              (psi' : ∀ w, (Fm.D x i).ntw.RCG ((Fm.ex x hx i).nch.twI w) (Q w) →*
                ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) (k' w))ˣ),
              ∀ w, (Fm.D x i).what₂.muAt w ≠ (Fm.D x i).what₂.mu0 → I.Ok ((Fm.ex x hx i).nch.twI w) ∧
                TwGoodAll (Fm.D x i) I ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (Q w) (k' w) (psi' w)

def TwGoodAtAll (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧ TwGoodAll D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

def QDistinctF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Formalism.MainNotions.Pk.EvL Fm fun x hx i => QDistinctAt (Fm.D x i) (Fm.ex x hx i).nch

end Formalism.MainNotions
