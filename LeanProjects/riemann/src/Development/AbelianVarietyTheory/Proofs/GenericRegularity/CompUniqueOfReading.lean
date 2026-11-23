import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem comp_unique_of_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp) (Z Z' : Comp Xo c), ((U.X k).dom).Nonempty → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z' f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → Z = Z' := by
  intro E _ _ _ H Dw l Xo c σ r U _ _ h k Z Z' _ hZ hZ'
  by_contra hne
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨χ, hχ, -, h1, h0⟩ := GlobalTheory.Reg.exists_idem_section E H Dw l Xo c hL h (hA h) Z
  have hd : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩
  have h2 := (hZ 0 0 hd χ hχ).2 ((hZ' 0 0 hd χ hχ).1 (h0 Z' (Ne.symm hne)))
  rw [h1] at h2
  exact one_ne_zero h2

end GlobalTheory.Reg
