import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialPartInBaseChange
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitStepOAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.MuBlockLoc
end GlobalTheory.MuBlockLoc
namespace GlobalTheory.MuBlockLoc
theorem mu_block_mem_alt : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa →
    (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  intro D Rw hL j σ π μ Pa hA hR hB
  have hgood : ∀ᶠ w in Filter.cofinite, ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧
      D.naut.unr (D.naut.locG μ w)) ∧ ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    refine Filter.Eventually.and (Filter.Eventually.and ?_ (D.naut.locG_unr_ae _)) ?_
    · exact (Filter.eventually_all_finite (List.finite_toSet Pa)).2 fun p _ => D.naut.locG_unr_ae p.π
    · exact Filter.eventually_all.2 fun k => (placesOver_finite D k).compl_mem_cofinite
  obtain ⟨w0, hw0, hs0⟩ := GlobalTheory.MuBlock.exists_split_not_mem D.nd hL.an.2.2.1 _ (Filter.eventually_cofinite.1 hgood)
  have hg0 : ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w0)) ∧ D.naut.unr (D.naut.locG μ w0)) ∧
      ∀ k : Fin 2, w0 ∉ placesOver D.host.E (D.host.g k) := by
    have h := hw0
    simp only [Set.mem_setOf_eq, not_not] at h
    exact h
  obtain ⟨⟨p0, hp0, hpt⟩, -⟩ := _root_.GlobalTheory.MuBlockLoc.split_step_o_alt D Rw hL j σ π μ Pa hA hR hB w0 hs0 hg0.2 hg0.1.1 hg0.1.2
  have hall : ∀ w, (((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧ D.naut.unr (D.naut.locG μ w)) ∧
      ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
      IsSplitPl D.host w → p0.d = D.R.t ∧ D.naut.frobEig (D.naut.locG p0.π w) =
        D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) :=
    fun w hw hs => (_root_.GlobalTheory.MuBlockLoc.split_step_o_alt D Rw hL j σ π μ Pa hA hR hB w hs hw.2 hw.1.1 hw.1.2).2 p0 hp0 hpt
  have htu : ∀ w, D.naut.unr (D.naut.locG μ w) →
      D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := fun w h => by
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ _) h (D.naut.etaTinv_def w).1
  obtain ⟨hd0, hf0⟩ := hall w0 hg0 hs0
  have ha0 : p0.a = 1 := by
    have h1 := D.naut.frobEig_card _ (hg0.1.1 p0 hp0)
    rw [hf0, D.naut.frobEig_card _ (htu w0 hg0.1.2), D.naut.locG_dim, D.naut.locG_dim] at h1
    exact h1.symm
  obtain ⟨a, π', d⟩ := p0
  dsimp only at ha0 hd0 hall hp0
  subst ha0 hd0
  have hν : π' = D.naut.tw μ D.naut.etaTinv := by
    refine hL.one π' _ ?_
    filter_upwards [hgood] with w hw hs
    rw [D.naut.unr_eq_lpUnr _ (hw.1.1 _ hp0), (hall w hw hs).2, ← D.naut.unr_eq_lpUnr _ (htu w hw.1.2)]
  subst hν
  exact hp0
end GlobalTheory.MuBlockLoc
end
end
