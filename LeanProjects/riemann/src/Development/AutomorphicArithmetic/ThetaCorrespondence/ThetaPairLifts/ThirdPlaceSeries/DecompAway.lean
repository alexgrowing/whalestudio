import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqAlgebraMapOfCharpoly
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent
namespace GlobalTheory.WeilDeligne.InertiaSplit
variable {l : ℕ} [Fact l.Prime]
end GlobalTheory.WeilDeligne.InertiaSplit
namespace GlobalTheory.WeilDeligne.InertiaSplit
variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end GlobalTheory.WeilDeligne.InertiaSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.WeilDeligne.InertiaSplit.decomp_away_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ p q : D.naut.LP w, D.naut.wdOf i ρ w = D.naut.lpSum p q → ∃ U U' : Submodule (Qbar (D.nd.l i)) (Fin a → Qbar (D.nd.l i)), IsCompl U U' ∧ Module.finrank (Qbar (D.nd.l i)) U = D.naut.lpDim p ∧ Module.finrank (Qbar (D.nd.l i)) U' = D.naut.lpDim q ∧ (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), (∀ v ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v ∈ U) ∧ (∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v ∈ U')) ∧ (D.naut.mono0 q → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ∀ c : Qbar (D.nd.l i), D.naut.inePol q σ = (X - C (D.naut.iotaQC i c)) ^ D.naut.lpDim q → ∀ v ∈ U', ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))).mulVec v = c • v)) := by
  intro _ hL D P i a ρ hρ w hw p q hpq
  have hw' : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have e1 := congrArg (P.T.e w) hpq
  rw [(P.wdOf i a ρ w).1, P.wd.away _ _ ρ w hw', P.T.sum] at e1
  obtain ⟨U, U', hC, h1, h2, h3, h4⟩ :=
    GlobalTheory.WeilDeligne.InertiaSplit.split_away hw' (D.naut.iotaQC i) ρ hρ _ _ e1
  refine ⟨U, U', hC, by rw [h1, P.T.dim], by rw [h2, P.T.dim], h3,
    fun hm σ hσ c hc => h4 ((P.T.mono0 w q).1 hm) σ hσ c ?_⟩
  rw [← P.T.inePol w q σ hσ, hc, P.T.dim]
end
end
