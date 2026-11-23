import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.Development
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCoverStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParamStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement

noncomputable section

namespace CompanionTheory.RgDs

open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.CoverDS GlobalTheory.Dec

theorem upqExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesUpqExists :=
  GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE

theorem exists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesExists :=
  GlobalTheory.Published.discreteSeriesExists_iff_upq.2 (upqExists_of hE)

theorem coverExists_of (hE : DSExists) : GlobalTheory.Published.DiscreteSeriesCoverExists :=
  GlobalTheory.Published.CoverSeries.of_upq (upqExists_of hE) (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)

def CoverUsed : Prop :=
  (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) ∧
  (∀ (p q : ℕ) (T : GrpData p q), 1 ≤ p + q → ∀ lam : Ix p q → ℚ, IsParam lam →
    ∀ R R' : DSRep T, HasParam R lam → HasParam R' lam → UnitEquiv R R') ∧
  ∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∀ R : DSRep T, HasParam R lam → HasTypes R lam

def ClassUsed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), GlobalTheory.DSId.IsHCDS ε lam π ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        Formalism.MainNotions.S.IsDS ε lam σ → UEquiv ε σ π

theorem classUsed_of (hE : DSExists) (hK : KTypesAbove) (hI : DSInfChar) : ClassUsed := by
  intro n ε lam hl
  obtain ⟨G, _, _, π, hπ⟩ := hE n ε lam hl
  refine ⟨G, _, _, π, ⟨⟨hπ.1, hπ.2.1, hπ.2.2.1, hπ.2.2.2.1, hπ.2.2.2.2.1⟩, hI n ε lam G π hl hπ, ?_,
    hK n ε lam G π hl hπ⟩, fun H _ _ σ hσ => CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ⟩
  obtain ⟨S, hS⟩ := hπ.2.2.2.2.2.1
  exact ⟨S, hS, fun S' hS' => CompanionTheory.DiscreteSeriesGap.GapInv.lowKMultOne_dec n ε lam G π hl hπ S' S hS' hS⟩

end CompanionTheory.RgDs
