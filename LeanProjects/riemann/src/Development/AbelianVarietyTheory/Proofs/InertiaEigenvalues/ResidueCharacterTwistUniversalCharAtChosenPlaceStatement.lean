import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlNeOfSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCharacter_twist_universalChar_at_chosen_place : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  first | exact @GlobalTheory.ResTwist.res_twist_spec | exact GlobalTheory.ResTwist.res_twist_spec | (intros; apply GlobalTheory.ResTwist.res_twist_spec <;> assumption)
