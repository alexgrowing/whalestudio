import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

theorem _root_.UpperTheory.KN.continuous_localCoefficientRep_twist :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), GoodR D.nd i r → ∀ x, Continuous fun g => (locOC C (rTwO D.nd i r x) g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) := by
  intro D i r w hw C hr x
  have h1 := GlobalTheory.PotDual.continuous_loc D i w hw _ (GlobalTheory.Pass.FamCont.stepCont D i r hr x).1
  have h2 : Continuous (fun y => C.inc y) :=
    continuous_induced_rng.2 continuous_subtype_val
  refine (h1.matrix_map h2).congr fun g => ?_
  ext a b
  rfl
