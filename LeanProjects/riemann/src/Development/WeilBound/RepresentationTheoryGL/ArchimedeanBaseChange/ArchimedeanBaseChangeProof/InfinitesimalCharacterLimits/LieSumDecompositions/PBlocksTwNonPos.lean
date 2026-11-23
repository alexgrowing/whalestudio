import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

theorem pE_shift (a r : ℕ) (c w : ℂ) :
    pE E a r (c + w * r * (Module.finrank ℚ E : ℂ)) = pE E a r c + w.re * r := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast this.ne'
  unfold pE
  have e : (c + w * r * (Module.finrank ℚ E : ℂ)).re = c.re + w.re * r * (Module.finrank ℚ E : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  rw [e]
  field_simp
  ring

theorem nonPos_tw {a : ℕ} (V : Submodule ℂ (Sm E a)) (w : ℂ) (haut : ∀ φ ∈ V, IsAutForm φ)
    (hV : ∀ φ ∈ V, ∀ r, 0 < r → r < a → ∀ c ∈ Exp r φ.1, pE E a r c + w.re * r ≤ 0) :
    SpectralAccumulation.NonPos (tw V w) := by
  intro φ hφ r hr hra c hc
  obtain ⟨ψ, hψ, rfl⟩ := Submodule.mem_map.1 hφ
  have h0 := expTw_holds E a ψ w (haut ψ hψ) r hr hra c hc
  have h1 := hV ψ hψ r hr hra _ h0
  have e : c = (c - w * r * (Module.finrank ℚ E : ℂ)) + w * r * (Module.finrank ℚ E : ℂ) := by ring
  rw [e, pE_shift]
  exact h1

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockTwistCharacters

end
