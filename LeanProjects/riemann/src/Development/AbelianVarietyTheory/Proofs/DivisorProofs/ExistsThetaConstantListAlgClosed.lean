import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveListMSqTorsionPolarisedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantMSqTorsionAlgClosedFibreStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_thList : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  intro S G _ _ L ρ hL hρ g m N K _ _ x θ hm hmK hN hP
  subst hN
  obtain ⟨pt, hinj, hpt, hall⟩ := GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre S G L g m K x hmK hP
  choose c hc using fun a => GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre S G L ρ hL hρ g m K x θ (pt a) hm hmK hP (hpt a)
  exact ⟨pt, c, hinj, hc, hall⟩

end GlobalTheory.UMin
