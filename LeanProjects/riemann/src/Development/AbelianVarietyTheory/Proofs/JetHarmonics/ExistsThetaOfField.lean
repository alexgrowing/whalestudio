import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.Jets.IsAppBox
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBFSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ColumnValueFSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory.BoxApp

namespace GlobalTheory.ThetaLift

theorem exists_theta_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L ((0 : ℕ) : ℤ) T, θ.pt = x := by
  refine ⟨⟨x, ⟨fun _ => 1⟩, ?_⟩, rfl⟩
  refine isGen_of_gm (M := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A x).left])
    (ε := ![((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ)]) _ fun w j j' h h' => ?_
  refine (map_one _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_one _)).symm)
  simp [trF, Fin.prod_univ_two]

theorem exists_theta_of_field : ∀ (K : Type) [Field K] (A : PolAV (Sp K)) (Y : Over (Sp K)) (F : Type) [Field F] (e : Y.left ≅ Sp F) (k : ℕ) (x : Y ⟶ A.A), x ^ k = 1 → ∃ θ : ThetaGrp A.A A.L (k : ℤ) Y, θ.pt = x := by
  intro K _ A Y F _ e k x hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact exists_theta_zero A.L x
  · have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    have : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
    have : Subsingleton Y.left := e.hom.homeomorph.toEquiv.subsingleton
    have : Nonempty Y.left := e.hom.homeomorph.toEquiv.nonempty
    exact GlobalTheory.BoxTheta.exists_theta GlobalTheory.firstFiveLaws.1.kerPow A hk x hx

end GlobalTheory.ThetaLift
