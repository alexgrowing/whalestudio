import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_key_section_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → (∀ k la γ, (U.X k).χ la γ = 1) → FnAlgClosed Xo c → 2 ≤ N → 2 < Module.finrank ℚ E / 2 → Nonempty (KeySec Xo c) := by
  first | exact @GlobalTheory.KeyFourth.nonempty_keySec | exact GlobalTheory.KeyFourth.nonempty_keySec | (intros; apply GlobalTheory.KeyFourth.nonempty_keySec <;> assumption)
