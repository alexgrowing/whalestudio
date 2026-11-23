import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementCOfCasselmanWallachStatement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.Choice

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ChoiceEx

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

theorem readsAt_conj {D : D7} (hs : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl}
    (h : ReadsAt i b w) : ReadsAt i (!b) (D.what₂.places.conj w) := fun x => by
  have h2 : IsIntegral ℤ (star ((x : ↥D.LL0) : D.what₂.LL)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) ((starRingEnd D.what₂.LL).comp (algebraMap ↥D.LL0 D.what₂.LL))
      (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
  let y : 𝓞 ↥D.LL0 := ⟨⟨_, hs x⟩, (isIntegral_algebraMap_iff (algebraMap ↥D.LL0 D.what₂.LL).injective).1 h2⟩
  have hy : ((y : ↥D.LL0) : D.what₂.LL) = star ((x : ↥D.LL0) : D.what₂.LL) := rfl
  rw [sideEmb_not i b hy, D.conj_val, ← hy]
  exact h y

theorem exists_settings_conj {D : D7} (hs : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hc : ∀ w : D.what₂.places.Pl, ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧ GlobalTheory.HeightCounting.SidePl D w i true) :
    ∃ s : D.what₂.places.Pl → D.ntw.Tw, (∀ v, ∃ b, ReadsAt (s v) b v) ∧ ∀ v, s (D.what₂.places.conj v) = s v := by
  choose t _ ht using hc
  have hr : ∀ w, ReadsAt (t w) true w := fun w x => Formalism.L2.emb0_mem_maximalIdeal_iff_val_pos_of_sidePl D w (t w) (ht w) (x : D.LL0)
  obtain ⟨o, ho⟩ := exists_orbitRep (D := D)
  refine ⟨fun v => t (o v), fun v => ?_, fun v => by simp only [(ho v).2]⟩
  rcases (ho v).1 with h | h
  · exact ⟨true, by simpa only [h] using hr v⟩
  · have h1 := readsAt_conj hs (hr (D.what₂.places.conj v))
    rw [D.what₂.places.conj_conj] at h1
    exact ⟨_, by simpa only [h] using h1⟩

theorem sc_of_sck {hL : GlobalTheory.Published.LocalLanglandsGL} (h : SCk hL) : SC hL :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H P x l => by
    obtain ⟨s, h1, h2⟩ := exists_settings_conj (D := Dof x) l.a.elem.star l.b.Bs.cover
    obtain ⟨c, -⟩ := H P x l s h1 h2
    exact ⟨c⟩)

theorem choices_exist : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SC hL :=
  fun hCo hCW hHM a b hL => sc_of_sck (GlobalTheory.T.statement_c_of_casselman_wallach hCo hCW hHM a b hL)

end GlobalTheory.HeightCounting.Up.ChoiceEx

end
