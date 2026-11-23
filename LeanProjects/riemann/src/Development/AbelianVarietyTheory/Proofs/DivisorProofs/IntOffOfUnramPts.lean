import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatTw

theorem intOff_of_unramPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), UnramPts Xo c B → ∀ (Z : Comp Xo c) (la : Weight Dw) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z la δ), IntOff B (δ + s.rho_vw) := by
  intro E _ _ _ H Dw l Xo c r U x B hB Z la δ s w hw
  obtain ⟨v, hv, hint⟩ := hB Z w hw
  have he := s.val_eq hv
  rcases hint s.sig with h | ⟨n, hn⟩
  · rw [he] at h; exact absurd h (EReal.coe_ne_top _)
  · rw [he] at hn
    exact ⟨n, EReal.coe_eq_coe_iff.1 hn⟩

end GlobalTheory.FlatTw
