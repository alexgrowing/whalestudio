import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLe
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLocusExponent_twistingSection_mul_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  first | exact @GlobalTheory.RefTwist.refExp_vp_add_le | exact GlobalTheory.RefTwist.refExp_vp_add_le | (intros; apply GlobalTheory.RefTwist.refExp_vp_add_le <;> assumption)
