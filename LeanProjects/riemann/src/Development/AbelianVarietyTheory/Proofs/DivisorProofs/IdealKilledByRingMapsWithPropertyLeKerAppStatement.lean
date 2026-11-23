import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealKilledByRingMapsWithPropertyLeKerApp
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealKilledByRingMapsWithProperty_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  first | exact @GlobalTheory.PtClosed.killIdeal_le_ker_app | exact GlobalTheory.PtClosed.killIdeal_le_ker_app | (intros; apply GlobalTheory.PtClosed.killIdeal_le_ker_app; all_goals assumption)
