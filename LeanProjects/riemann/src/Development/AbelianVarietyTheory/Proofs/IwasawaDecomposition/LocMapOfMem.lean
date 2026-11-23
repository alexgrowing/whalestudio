import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphLoc

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

open Classical in

def locMap (c : AlgChart p σ d) (f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) : ChartMap p σ d :=
  fun c₀ y ξ =>
    if y ∈ c.e.source ∧ f (c.e y, WithLp.toLp 2 (c₀.dtrans c y ξ)) ∈ c.e.target then
      c.e.symm (f (c.e y, WithLp.toLp 2 (c₀.dtrans c y ξ)))
    else y

theorem locMap_of_mem (c c₀ : AlgChart p σ d) (f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d)
    {y : CxPts p σ} {ξ : Fin d → ℂ} (h : y ∈ c.e.source ∧ f (c.e y, WithLp.toLp 2 (c₀.dtrans c y ξ)) ∈ c.e.target) :
    locMap c f c₀ y ξ = c.e.symm (f (c.e y, WithLp.toLp 2 (c₀.dtrans c y ξ))) := if_pos h

theorem dtrans_smul (c c₀ : AlgChart p σ d) (y : CxPts p σ) (t : ℝ) (ξ : Fin d → ℂ) :
    c₀.dtrans c y (t • ξ) = t • c₀.dtrans c y ξ := by
  funext b
  simp only [AlgChart.dtrans, Pi.smul_apply]
  rw [WithLp.toLp_smul, ContinuousLinearMap.map_smul_of_tower]
  rfl

end GlobalTheory.ChernReg.ExphLoc
