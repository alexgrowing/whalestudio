import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticesGlueToVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelSectionsCompatibleStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory.BplusDescent

theorem exists_cover_vectorBundles : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (J : Type) [Finite J] (h : ℕ) (L : J → ∀ U : AffOp B.X, Submodule U.Bp (Fin h → U.Bp)) (T : Set (Σ U : AffOp B.X, U.Bp)), T.Finite → (∀ j U, Module.Finite U.Bp (L j U) ∧ Module.Projective U.Bp (L j U) ∧ ∀ x : Fin h → U.Bp, (p : U.Bp) • x ∈ L j U) → (∀ j (U U' : AffOp B.X) (hle : U'.1 ≤ U.1), L j U' = Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (L j U : Set (Fin h → U.Bp)))) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : J → B'.X.Modules) (ι : ∀ j, E j ⟶ freeModule B'.X (Fin h)), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ IsFinite f.f ∧ (∀ U, Function.Injective (γ U)) ∧ (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), γ U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) ∧ (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)), γ U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) ∧ (∀ t ∈ T, t.2 ∈ Set.range (γ t.1)) ∧ ∀ j, GlobalTheory.VB.IsVB (E j) h ∧ Mono (ι j) ∧ ∀ U : AffOp B.X, L j U = Submodule.span U.Bp {x | ∃ s : Γ(E j, f.f ⁻¹ᵁ U.1), ∀ i, x i = γ U (((GlobalTheory.VB.isFrame_freeFrame B'.X (Fin h)).basis le_top).repr ((ι j).app _ s) i)} := by
  intro O _ _ _ p _ _ _ B hB J _ h L T hT hL hc
  obtain ⟨K', hK', hTK, hD⟩ := GlobalTheory.T.exists_finite_extension_lattices_descend O p B J h L T hT hL hc
  obtain ⟨B', f, γ, hn, hd, hfin, hinj, halg, hres, hrange⟩ := GlobalTheory.T.exists_normal_finite_model_of_extension O B hB K' hK'
  obtain ⟨E, ι, hE⟩ :=
    GlobalTheory.T.normal_model_sections_compatible O p B B' f K' γ hfin hinj halg hres hrange J h L (fun j U => ⟨hD j U, (hL j U).2.2⟩) hc
  refine ⟨B', f, γ, E, ι, hn, hd, hfin, hinj, halg, hres, fun t ht => ?_, hE⟩
  have : t.2 ∈ (γ t.1).range := by rw [hrange]; exact hTK t ht
  exact this

end GlobalTheory.BplusDescent
