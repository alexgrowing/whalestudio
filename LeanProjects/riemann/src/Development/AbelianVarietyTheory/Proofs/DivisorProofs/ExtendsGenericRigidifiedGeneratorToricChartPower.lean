import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqGeneratorFactorialBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseUnitRigidifiedGenericGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGeneratorDivBaseUnitEqGenericStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem extendGenAt_chartRing : ∀ (k : Type) [Field k] (m n : ℕ),
    GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  intro k _ m n
  have : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  have := GlobalTheory.isRegularRing_of_isRegularLocalRing (ChartRing k m n)
  have : IsDomain (ChartRing k m n) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).1
  have : UniqueFactorizationMonoid (ChartRing k m n) := GlobalTheory.ThetaExtend.ufd_of_regular _
  intro G _ _ hG eA heA N r hr hc
  have := hG.smooth
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨a, u, hu, hf⟩ := GlobalTheory.T.exists_const_mul_eq_generator_factorial_base _ _ G _ _ _ N.L r inferInstance inferInstance inferInstance
    (IsPullback.of_hasPullback _ _) N.isLB hr
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator _ _ G (eSec G) (Over.w η[G]) eA heA N.L N.rig r N.isLB N.rigGen hc a u hu hf
  exact GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic _ _ G _ _ _ pullback.condition N.L r a b hb u hu hf

end GlobalTheory.ChartCubExt
