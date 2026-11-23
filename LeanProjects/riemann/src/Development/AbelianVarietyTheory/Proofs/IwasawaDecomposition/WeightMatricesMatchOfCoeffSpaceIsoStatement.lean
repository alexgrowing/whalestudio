import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K) (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam), (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam), (∀ γ x, T' (ρ' γ x) = rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat γ) (T' x)) → GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' := by
  first | exact @GlobalTheory.CoefMatch.wtMatch_of_coef | exact GlobalTheory.CoefMatch.wtMatch_of_coef | (intros; apply GlobalTheory.CoefMatch.wtMatch_of_coef <;> assumption)
