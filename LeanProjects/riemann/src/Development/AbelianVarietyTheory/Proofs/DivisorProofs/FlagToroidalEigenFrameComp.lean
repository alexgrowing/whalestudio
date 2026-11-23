import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentStructureMapSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenframeOnAffineOpenStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

theorem exists_cell_pt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → IsIntegral V.toScheme → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (u : Cell.Coord Dw → Γ((Φ.C k).Y.X, Cell.cellOpen (Φ.C k) hV f₀ w)), Cell.IsCoord (Φ.C k) hV f₀ w u → ∀ y : (Φ.C k).Y.X, y ∈ Cell.cellOpen (Φ.C k) hV f₀ w → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ V.toScheme) (a : Cell.Coord Dw → Γ(Spec (.of Ω), ⊤)), ∃ p : Spec (.of Ω) ⟶ (Cell.cellOpen (Φ.C k) hV f₀ w).toScheme, p ≫ Cell.cellMap (Φ.C k) hV f₀ w = x ∧ ∀ i, p.appTop (Cell.coordTop (Φ.C k) hV f₀ w u i) = a i := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k V hV φV f₀ hstr hVi w u hu y hy Ω _ _ x a
  let ψ : Γ(gen Z, V) →+* Ω := (Spec.preimage (x ≫ hV.isoSpec.hom)).hom
  have hψ : spMap ψ ≫ hV.fromSpec = x ≫ V.ι := by
    rw [← hV.isoSpec_inv_ι]
    show Spec.map (Spec.preimage (x ≫ hV.isoSpec.hom)) ≫ _ = _
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]
  let a' : Coord Dw → Ω := fun i => (Scheme.ΓSpecIso (.of Ω)).hom (a i)
  obtain ⟨g, hg⟩ := exists_frameIn hV f₀ w ψ hψ a'
  have hst : (x ≫ V.ι) ≫ genStr Z = spMap (ψ.comp φV) := by
    rw [← hψ, Category.assoc, hstr, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts Ω (ψ.comp φV) (x ≫ V.ι) hst g
  have hik : i = k := GlobalTheory.T.flag_toroidal_eigenframe_on_affine_open Φ k hV f₀ hstr hVi w y hy Ω ψ (x ≫ V.ι) hψ g a' hg i p hp hc
  subst hik
  obtain ⟨q, hq, hqa⟩ := GlobalTheory.T.flag_component_structure_map_spec (Φ.C i) hV f₀ hstr w u hu Ω ψ (x ≫ V.ι) hψ g a' hg p hp hc
  refine ⟨q, ?_, fun j => ?_⟩
  · rw [← cancel_mono V.ι, Category.assoc, cellMap_ι, ← Category.assoc, hq, hp]
  · exact (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso (.of Ω)).hom) (hqa j)

end GlobalTheory.ShFam.Cell
