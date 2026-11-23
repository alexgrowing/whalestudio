import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NFunAddOneLtEExpAddCen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGridUnitGapFieldContainsValuesStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GridLg

theorem lamOf_ok (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (cDep b : ℝ) (G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩)
    (w0 : HeightOneSpectrum (𝓞 D.host.E)) (h : GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0) :
    (GlobalTheory.BigTop.Fun.lamOf G).Ok := by
  classical
  refine ⟨⟨?_, h.distinct, h.splits⟩, GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk D L _ G w0 h, fun j a g => ?_⟩
  · have h1 := G.pl.basePlace_over_qZero
    have h2 := G.pl.w_over G.pl.v0 (Finset.mem_insert_self _ _)
    show ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w G.pl.v0).asIdeal
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ (G.pl.w G.pl.v0).asIdeal := by
      rw [← h2] at h1; exact h1
    rwa [map_natCast] at h3
  · exact GlobalTheory.BigTop.Fun.nFun_add_one_lt_eExp_add_cen 1 j a g

theorem exists_grid : PrN → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x =>
    ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧
      (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  intro _ cDep
  have hd : AllSt fun K _ _ _ _ _ x => ∃ w0, GlobalTheory.LamTie.PlacesOk (Dof x).host (AbsolutelyIrreducibleSpan.q0 (Dof x)) w0 :=
    (Step.of_evLgG GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices).trans (Step.of_all fun K B f T _ hk _ H w _ P x => (H hk T w x.o.Z).2.2.2.2.2.2)
  refine (StepW.and (GlobalTheory.T.exists_grid_unit_gap_field_contains_values cDep) hd).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  obtain ⟨G, hG⟩ := H.1 P x
  obtain ⟨w0, h0⟩ := H.2 P x
  exact ⟨G, hG, lamOf_ok _ _ _ _ G w0 h0, x.m.z.lev.C.trans rfl, rfl⟩

end GlobalTheory.HeightCounting.Up.GridLg

end
