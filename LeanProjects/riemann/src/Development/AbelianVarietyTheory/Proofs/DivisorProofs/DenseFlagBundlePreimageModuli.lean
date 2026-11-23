import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem isOpenMap_scheme_comp {X₁ X₂ X₃ : Scheme.{0}} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (hf : IsOpenMap f)
    (hg : IsOpenMap g) : IsOpenMap (f ≫ g) := hg.comp hf

theorem isOpenMap_cbase {X : Scheme.{0}} {T : Type} (m : T → ℕ) (U : X.affineOpens) : IsOpenMap (cbase m U) := by
  haveI : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact isOpenMap_scheme_comp (MvPolynomial.isOpenMap_comap_C) U.2.fromSpec.isOpenEmbedding.isOpenMap

theorem dense_genMap_preimage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ
  have hcell : ∀ b w, IsOpenMap (κ b w ≫ π) := fun b w => by
    rw [hZ.plk.base b w]; exact isOpenMap_cbase _ _
  have hπ : IsOpenMap π := by
    intro O hO
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hZ.cover z
    refine ⟨(κ b w ≫ π) '' (κ b w ⁻¹' O), ?_, hcell b w _ (hO.preimage (κ b w).continuous), y, hz, rfl⟩
    rintro _ ⟨y', hy', rfl⟩
    exact ⟨κ b w y', hy', rfl⟩
  have hid : IsIso (spMap (RingHom.id c.F)) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]; infer_instance
  have he : genMap π = pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F)) ≫ π ≫
      inv (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    rw [← cancel_mono (pullback.fst Y.s (spMap (RingHom.id c.F)))]
    simp only [genMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hgen : IsOpenMap (genMap π) := by
    rw [he]
    exact isOpenMap_scheme_comp (pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))).isOpenEmbedding.isOpenMap
      (isOpenMap_scheme_comp hπ (inv (pullback.fst Y.s (spMap (RingHom.id c.F)))).isOpenEmbedding.isOpenMap)
  exact Y.jQ_dense.preimage hgen

end GlobalTheory.FlagMod.FieldFlag
