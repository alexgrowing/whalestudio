import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalization
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contains_after_localization : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), Built A M C tup big L → ∀ i : L.X.nd.Loc, Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) ∧ Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) ∧ (Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i) ∧ (ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i) ∧ (∀ S, Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S) ∧ ((∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r) ∧ ((∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔ ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ) := by
  first | exact @GlobalTheory.CoefDuty.MemberO.member_duties | exact GlobalTheory.CoefDuty.MemberO.member_duties | (intros; apply GlobalTheory.CoefDuty.MemberO.member_duties <;> assumption)
