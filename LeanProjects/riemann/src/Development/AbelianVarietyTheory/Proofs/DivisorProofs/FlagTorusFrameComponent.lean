import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentFramePermutation

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem exists_lands_of_mem_cellOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (y : (Φ.C k).Y.X), y ∈ Cell.cellOpen (Φ.C k) hV f₀ w → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (ψ : Γ(gen Z, V) →+* Ω) (a : Cell.Coord Dw → Ω), Cell.Lands Φ hV f₀ w k ψ a := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k V hV φV f₀ hstr w y hy
  obtain ⟨u, hu⟩ := exists_isCoord (Φ.C k) hV f₀ w
  let y' : (cellOpen (Φ.C k) hV f₀ w).toScheme := ⟨y, hy⟩
  let Ω : Type := AlgebraicClosure ((cellOpen (Φ.C k) hV f₀ w).toScheme.residueField y')
  let p : Spec (.of Ω) ⟶ (cellOpen (Φ.C k) hV f₀ w).toScheme :=
    Spec.map (CommRingCat.ofHom (algebraMap ((cellOpen (Φ.C k) hV f₀ w).toScheme.residueField y') Ω)) ≫ (cellOpen (Φ.C k) hV f₀ w).toScheme.fromSpecResidueField y'
  obtain ⟨x, hx⟩ : ∃ x, (p ≫ (cellOpen (Φ.C k) hV f₀ w).ι) ≫ (Φ.C k).π = x := ⟨_, rfl⟩
  obtain ⟨ω, hω, φΩ, M, hωx, hφx, hM, ⟨g, hg⟩, hcar⟩ := point_data (Φ.C k) hV f₀ w u hu Ω p x hx
  subst hωx
  have hφ : φΩ = ω.comp φV := by
    have h1 : spMap φΩ = spMap (ω.comp φV) := by
      rw [← hφx, Category.assoc, hstr, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  subst hφ
  refine ⟨Ω, inferInstance, inferInstance, ω, fun i => (Scheme.ΓSpecIso (.of Ω)).hom (p.appTop (coordTop (Φ.C k) hV f₀ w u i)), g,
    ⟨M, fun τ i => hg τ i, fun τ => hM τ⟩, p ≫ (cellOpen (Φ.C k) hV f₀ w).ι, hx, ?_⟩
  refine hcar g (fun τ => 1) (fun τ i => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne) (fun τ i => by simp) ?_
  intro τ i
  rw [hg τ i]
  simp [Matrix.one_apply]

end GlobalTheory.ShFam.Cell
