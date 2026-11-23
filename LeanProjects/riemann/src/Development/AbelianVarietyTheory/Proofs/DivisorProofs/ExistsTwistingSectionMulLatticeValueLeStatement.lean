import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLe
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistingSection_mul_lattice_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c) (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G, ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.TwMulOne.exists_latW_val_le | exact GlobalTheory.TwMulOne.exists_latW_val_le | (intros; apply GlobalTheory.TwMulOne.exists_latW_val_le <;> assumption)
