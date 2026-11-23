import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqualStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWdStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugationStatement

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CaraianiAboveL

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.CaraianiLocalGlobal →
    GlobalTheory.Published.LocalGlobalAboveL := by
  intro hF hL hC E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh r wt HT hG P AI hT w A h O _ _ _ Bw hj σ hσ rc hrc
  obtain ⟨R, hRc, hRs, hRaway, hRabove⟩ := hC E Ω l ι a ha π hc hcoh
  have htr : ∀ (w' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w'.asIdeal → ∀ (A' : ValuationSubring Ω)
      (h' : IsPlaceOver A' w') (τ : Weil h'), (R (τ : G E Ω)).val.trace = (r (τ : G E Ω)).val.trace := by
    intro w' hl A' h' τ
    obtain ⟨rc', hrc', -⟩ := hL.1 E Ω A' w' h'
    obtain ⟨σ', hσ', -⟩ := LocEx.exists_isLocComp hF E a π w'
    exact GlobalTheory.T.weil_trace_eq_of_same_wd E Ω l ι a R r w' A' h' (rc' (algNorm σ')) hl (hRaway w' hl A' h' rc' hrc' σ' hσ')
      (hG.away w' hl A' h' rc' hrc' σ' hσ') τ
  obtain ⟨p, hp⟩ := GlobalTheory.T.semisimple_conj_of_trace_equal E Ω l a R r hRc hG.cont hRs hG.ss htr
  obtain ⟨hpst, hR⟩ := hRabove P AI hT w A h O Bw hj
  have hwd := GlobalTheory.T.fontaineParameter_invariant_under_conjugation E Ω l ι a P AI hT w A h O Bw hj (R.comp (Dec (F := E) A).subtype)
    (r.comp (Dec (F := E) A).subtype) p (fun g => hp g) hpst
  rw [hwd.2]
  exact hR σ hσ rc hrc

end GlobalTheory.CaraianiAboveL

end
