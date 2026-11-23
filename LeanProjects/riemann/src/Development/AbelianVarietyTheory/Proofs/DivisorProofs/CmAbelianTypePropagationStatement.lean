import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianTypePropagation
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.GroupBplus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_type_propagation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsOfType Dw t → ∃ GG act pol θ ε τ, IsPropG (p := p) Dw t GG act pol θ ε τ := by
  first | exact @GlobalTheory.GroupBplus.Closed.exists_isPropG | exact GlobalTheory.GroupBplus.Closed.exists_isPropG | (intros; apply GlobalTheory.GroupBplus.Closed.exists_isPropG <;> assumption)
