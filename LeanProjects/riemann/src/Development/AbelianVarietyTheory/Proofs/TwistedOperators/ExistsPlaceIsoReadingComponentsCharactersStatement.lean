import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placeIso_reading_components_characters : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  first | exact @GlobalTheory.FlipMatch.exists_placeIso_chars | exact GlobalTheory.FlipMatch.exists_placeIso_chars | (intros; apply GlobalTheory.FlipMatch.exists_placeIso_chars <;> assumption)
