import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H w → IsCentreSet H.bar q ψ w → ∃ ψ' : InvFun (𝓞 E), IsPolyFan H.bar q ψ' ∧ IsTwInv H ψ' ∧ Subordinate H.bar q ψ' ψ ∧ IsStarOf H.bar q ψ w ψ' := by
  first | exact @GlobalTheory.PolFan.exists_starSubdivision | exact GlobalTheory.PolFan.exists_starSubdivision | (intros; apply GlobalTheory.PolFan.exists_starSubdivision <;> assumption)
