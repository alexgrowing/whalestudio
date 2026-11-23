import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIso
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_transport_along_generating_iso : ∀ {X : Scheme.{0}} {M L : LB X} (e : LB.Iso M L), e.IsGen → M.IsLB → L.IsLB →
    ∀ σ : L.Sec, ∃ σ' : M.Sec, GlobalTheory.Cartier.SecMaps e σ' σ ∧ Out.nonzeroLocus σ ≤ Out.nonzeroLocus σ' := by
  first | exact @GlobalTheory.SecTransport.main | exact GlobalTheory.SecTransport.main | (intros; apply GlobalTheory.SecTransport.main <;> assumption)
