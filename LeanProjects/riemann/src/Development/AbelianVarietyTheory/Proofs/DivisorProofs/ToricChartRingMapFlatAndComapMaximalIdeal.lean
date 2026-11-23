import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.LocRegFlat

theorem germ_flat {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.Flat := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

theorem chartHom_flat_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx he mm hmm hmem
  have key : GlobalTheory.LocReg.chartHom Y U ξ hx = ((Y.X.presheaf.germ U.1 (genι Y (ξ (closedPoint _))) hx ≫
      (genι Y).stalkMap (ξ (closedPoint _))) ≫ Scheme.stalkClosedPointTo ξ).hom := by
    have h := (genι Y).germ_stalkMap U.1 (ξ (closedPoint _)) hx
    unfold GlobalTheory.LocReg.chartHom
    rw [h]; rfl
  rw [key]
  simp only [CommRingCat.hom_comp]
  have hg := germ_flat U.2 _ hx
  have hs : ((genι Y).stalkMap (ξ (closedPoint _))).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  refine ⟨(hg.comp hs).comp he.1, ?_⟩
  symm
  refine hmm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top) ?_
  intro f hf
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hmem f hf
  rw [Scheme.mem_basicOpen]
  simp only [RingHom.comp_apply] at hu
  exact isUnit_of_map_unit ((genι Y).stalkMap _).hom _ (isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom _ hu)
  exact hx
end GlobalTheory.LocRegFlat
