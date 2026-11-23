import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem unitChartAt_of_mem_basicOpen_p : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X),
    x ∈ X.basicOpen (p : Γ(X, ⊤)) → UnitChartAt p Xw K x := by
  intro p _ X Xw K x hx
  obtain ⟨W', hW', hxW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  have hW'a : IsAffineOpen W' := hW'
  refine ⟨Γ(X, W'), inferInstance, hW'a.fromSpec, 1, inferInstance, ?_, ?_⟩
  · rw [hW'a.range_fromSpec]; exact hxW
  · intro φ _
    exfalso
    have hu : IsUnit ((p : ℕ) : Γ(X, W')) := by
      have := (X.toRingedSpace.isUnit_res_basicOpen (p : Γ(X, ⊤))).map
        (X.presheaf.map (homOfLE hWle).op).hom
      simp only [map_natCast] at this
      erw [map_natCast] at this
      exact this
    have h2 := hu.map φ
    rw [map_natCast] at h2
    exact GlobalTheory.PadicComplexHost.not_isUnit_p p h2

end GlobalTheory.FlatModel
