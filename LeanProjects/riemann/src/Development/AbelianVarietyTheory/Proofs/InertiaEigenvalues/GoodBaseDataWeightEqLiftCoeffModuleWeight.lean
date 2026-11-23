import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLiftWeight

theorem c_eq {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)}
    (hL : L.Is μ0) (hB : B.Good) (hmu : B.mu0 = L.mu0 ((j : ℕ) + 1)) (τ : D.what₂.Tau) :
    B.w.c τ = GlobalTheory.ConjTwist.liftC D j τ := by
  have h1 := hB.inf τ
  rw [hmu] at h1
  have h2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 (GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ)
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have h3 := GlobalTheory.ConjTwist.liftC_cast D j τ
  rw [hp, hq] at h2
  have h4 : (B.w.c τ : ℚ) = (GlobalTheory.ConjTwist.liftC D j τ : ℚ) := by
    rw [h3]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS, GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS] at *
    linarith
  exact_mod_cast h4

theorem lam_eq : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  intro D T0 L μ0 j B hL hB hmu hap ham
  funext τ
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have hc := c_eq hL hB hmu τ
  have e1 := hB.wt.lam_eq τ
  have e2 := (GlobalTheory.ConjTwist.liftWeight_good D j).lam_eq τ
  rw [hp, hq, hap τ, ham τ, hc] at e1
  have key : (B.w.lam τ).w = (FWT.lamV D j τ).w := funext fun a => (e1 a).trans (e2 a).symm
  generalize B.w.lam τ = x at key
  generalize FWT.lamV D j τ = y at key
  cases x
  cases y
  cases key
  rfl

end GlobalTheory.BaseLiftWeight
