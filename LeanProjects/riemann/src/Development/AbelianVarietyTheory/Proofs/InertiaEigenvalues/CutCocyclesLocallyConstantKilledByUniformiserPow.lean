import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPresCutCocycleLocalCoefficient
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsCocycleTorsionOfHasPres
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ContinuousLocalCoefficientRepTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
theorem _root_.GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (lam : ↥(OL C.LL)), Irreducible lam → GoodR D.nd i r → TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), ∀ z ∈ cutCoc i w hw r Set.univ M,
    ∃ a : ℕ, (fun g => liftQ C.le k (z g)) ∈ divisibleCocycles (latC C (locOC C M)) ∧ ∀ g, lam ^ a • liftQ C.le k (z g) = 0 := by
  intro D i r w hw C lam hlam hGood _ k M z hz
  have hG := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  have hdom : IsDomain ↥(OL C.LL) := hG.1.1
  have hdvr : @IsDiscreteValuationRing ↥(OL C.LL) _ hdom := hG.1.2.1
  have hfr : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := hG.1.2.2
  have htop : IsTopologicalRing ↥C.LL.1 := hG.2.2.2.1
  have hopen := hG.2.2.2.2
  have h1 := UpperTheory.KN.continuous_localCoefficientRep_twist D i r w hw C hGood
  have h2 := UpperTheory.KN.hasPres_cutCocycle_localCoefficient D i r w hw C M z hz
  have h3 := @UpperTheory.KN.exists_cocycle_torsion_of_hasPres (Br.G D.nbr i w hw) ↥(OL C.LL) ↥C.LL.1 _ _ _ hdom hdvr _ _ htop _ hfr Subtype.val_injective lam _ _ _
    (fun x => locOC C (rTwO D.nd i r x)) (locOC C M) (fun g => liftQ C.le k (z g)) hlam hopen h1
  exact h3 h2
