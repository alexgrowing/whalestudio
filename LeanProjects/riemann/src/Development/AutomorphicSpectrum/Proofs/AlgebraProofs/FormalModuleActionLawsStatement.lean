import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalModuleActionLaws
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_module_action_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), B.A.act 0 = 0 ∧ (∀ n : ℕ, B.A.act ((n + 1 : ℕ) : O) = B.G.add (B.A.act (n : O)) (pt R d 0)) ∧ (∀ a b, comp1 (B.A.act a) (B.A.act b) = comp1 (B.A.act b) (B.A.act a)) ∧ ∀ n, AxOne (pow1 B n) ∧ AxOne (pow2 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.NatAct.act_nat_iterated | exact GlobalTheory.CompanionTheory.Ar.Conj.NatAct.act_nat_iterated | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.NatAct.act_nat_iterated <;> assumption)
