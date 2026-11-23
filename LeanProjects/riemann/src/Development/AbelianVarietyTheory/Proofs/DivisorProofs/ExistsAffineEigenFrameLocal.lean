import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

set_option autoImplicit false

namespace GlobalTheory.ShFam.IntCell

theorem exists_integral_eigFrame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, Smooth (genStr Z) → ∀ z : gen Z, ∃ (V : (gen Z).Opens) (hV : IsAffineOpen V) (φV : c.F →+* Γ(gen Z, V)) (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), z ∈ V ∧ IsIntegral V.toScheme ∧ hV.fromSpec ≫ genStr Z = spMap φV := by
  intro E _ _ _ H Dw l Xo c O _ β Z hsm z
  obtain ⟨U, hU, φ, f, hzU, hs, -⟩ :=
    GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z z
  haveI : GlobalTheory.IsNormalScheme (gen Z) := by
    have hY : ∀ y : Sp c.F, IsDomain ((Sp c.F).presheaf.stalk y) ∧
        IsIntegrallyClosed ((Sp c.F).presheaf.stalk y) :=
      (GlobalTheory.isNormalScheme_iff _).1 (GlobalTheory.IsNormalScheme.spec (CommRingCat.of c.F))
    exact (GlobalTheory.isNormalScheme_iff _).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (genStr Z) hY)
  haveI : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  let C : Set (gen Z) := irreducibleComponent z
  have hC : C ∈ irreducibleComponents (gen Z) := irreducibleComponent_mem_irreducibleComponents z
  have hCo : IsOpen C := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hC
  have hzC : z ∈ C := mem_irreducibleComponent
  obtain ⟨V, hV, hzV, hVle⟩ := exists_isAffineOpen_mem_and_subset (X := gen Z)
    (U := U ⊓ ⟨C, hCo⟩) (x := z) ⟨hzU, hzC⟩
  have hVU : V ≤ U := fun y hy => (hVle hy).1
  have hVC : (V : Set (gen Z)) ⊆ C := fun y hy => (hVle hy).2
  have hirr : IsIrreducible (V : Set (gen Z)) :=
    ⟨⟨z, hzV⟩, hC.1.2.open_subset V.isOpen hVC⟩
  haveI : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  have hint : IsIntegral V.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  let ρ : Γ(gen Z, U) →+* Γ(gen Z, V) := ((gen Z).presheaf.map (homOfLE hVU).op).hom
  have hρ : spMap ρ ≫ hU.fromSpec = hV.fromSpec := hU.map_fromSpec hV (homOfLE hVU).op
  obtain ⟨g, -⟩ := GlobalTheory.ShFam.Spread.exists_bc f ρ (φ' := ρ.comp φ) rfl
    (x' := hV.fromSpec ≫ genι Z) (by rw [← Category.assoc, hρ])
  refine ⟨V, hV, ρ.comp φ, g, hzV, hint, ?_⟩
  rw [← hρ, Category.assoc, hs, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]

end GlobalTheory.ShFam.IntCell
