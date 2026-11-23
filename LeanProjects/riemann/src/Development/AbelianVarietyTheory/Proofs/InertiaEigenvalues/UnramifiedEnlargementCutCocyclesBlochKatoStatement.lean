import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKato
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  first | exact @GlobalTheory.UseLoc.Cases.main | exact GlobalTheory.UseLoc.Cases.main | (intros; apply GlobalTheory.UseLoc.Cases.main <;> assumption)
