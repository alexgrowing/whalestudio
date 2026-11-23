import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimple
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_factorization_semisimple : ∀ (D : D7), Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) → (∀ g, ((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly = ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly * ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))) → GlobalTheory.LocalInv.Cont D.nd i ρ := by
  first | exact @GlobalTheory.SSComplement.cont | exact GlobalTheory.SSComplement.cont | (intros; apply GlobalTheory.SSComplement.cont <;> assumption)
