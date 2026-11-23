import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSchAlt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.EvXTemperate

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.SiegelWeilFormula.KFock

theorem piProdSch (W : Type) [Fintype W] (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (S : W → 𝓢(V, ℂ)) :
    ∃ T : 𝓢(W → V, ℂ), ∀ y, T y = ∏ w, S w (y w) :=
  piProdSch' W S

theorem fPSch {m n : ℕ} (P : PositivityTheory.Rg.Sw.PX m n) {c : ℝ} (hc : 0 < c) :
    ∃ S : 𝓢(Fin m → Fin n → ℂ, ℂ), ∀ x, S x = PositivityTheory.Rg.Sw.evX P x * PositivityTheory.Rg.Sw.gs c x := by
  obtain ⟨G, hG⟩ := gsSch m n hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => PositivityTheory.Rg.Sw.evX P x) G, fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (evX_temperate P), hG, smul_eq_mul]

end PositivityTheory.SiegelWeilFormula.KFock

end
