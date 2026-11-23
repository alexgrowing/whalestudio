import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Slots
variable {X : Type} [TopologicalSpace X] {e : ℕ}

def positionPot (th Pn : LocPot X) (f : X → ℝ) (i : ℕ) : Fin e → LocPot X :=
  fun j => (if (j : ℕ) < i then th else Pn) + LocPot.ofFun (if (j : ℕ) < i then f else fun _ => 0)

end Slots

section Lines
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

def muVert (Hd : HodgeData D) (B : ℕ) : HermLine J :=
  hermOfFun J (muTwDeg Hd B) fun z => (muLine Hd).h z * ∏ p ∈ D.SB B, D.vertFactor p z

def limTop (Hd : HodgeData D) (B : ℕ) (Nb : HermLine J) : ℝ :=
  II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
    ∑ i ∈ Finset.range (D.n + 1), ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z))

end Lines
end GlobalTheory.CompanionTheory.Ar.Cusp
