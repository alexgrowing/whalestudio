import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatWachLetterRingCompletionOfDenseSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpansStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationGammaStableAndSubOneMemPiSmulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationFrobeniusMemUpToQPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationQPowerMemFrobeniusSpanStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CokerFin

set_option maxHeartbeats 1000000 in

theorem coker_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  intro D HW F Cm l _ K s LL h W E C T₀ T₁ T₂ ι π h0 h1 h2 hs
  have hP : WachCharacterisationLattice W := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h
  have hp10 : p10 W T₂ := hP T₂ h2
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hfl : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_wachLetterRing_completion_of_dense_saturated ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) ((D.loc l).PD K).p W.EE W.EE_π
      W.EE_complete W.EE_dense W.EE_sat
  obtain ⟨hfree, hbc⟩ := GlobalTheory.T.wachSaturation_image_free_and_spans D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hs hfl
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.saturation_gamma_stable_of_good D HW F l K s LL h T₁ T₂ π h1 h2
  have hS := hp10 _ hfree hbc hg1 hg2 (GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power D HW F l K s LL h T₁ T₂ π h1 h2)
    (GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span D HW F l K s LL h T₁ T₂ π h1 h2 hfree hbc)
  obtain ⟨c, hc⟩ := GlobalTheory.NL.Coker.uniform (W.N_fg T₂) hS.ge
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩ := hc z hz
  exact ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩

end GlobalTheory.NL.CokerFin
