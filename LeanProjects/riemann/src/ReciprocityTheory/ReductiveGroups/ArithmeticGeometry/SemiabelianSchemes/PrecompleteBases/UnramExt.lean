import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Unramified.LocalRing

set_option autoImplicit false

noncomputable section

open IsLocalRing Polynomial
open scoped IntermediateField

namespace ReciprocityTheory.ChartRestriction.G.Semi.Unr

open ReciprocityTheory.ChartRestriction.G.Semi.Nb

theorem unramExt : ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by
  intro V _ _ _ _ k' _ _ _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField V) k'
  have hint : IsIntegral (ResidueField V) α := .of_finite (ResidueField V) α
  obtain ⟨f, hfg, hdeg, hf⟩ := exists_monic_lift (minpoly (ResidueField V) α) (minpoly.monic hint)
  have hg : Irreducible (f.map (residue V)) := hfg ▸ minpoly.irreducible hint
  have := isDomain f hf hg
  have := isLocal f hf hg
  have := dvr f hf hg
  have := complete f hf hg
  have := locHom f hf hg
  have := finite f hf

  let e₁ : ResidueField (AdjoinRoot f) ≃+* AdjoinRoot (minpoly (ResidueField V) α) :=
    (resEquiv f hf hg).trans (AdjoinRoot.algEquivOfEq (ResidueField V) _ _ hfg).toRingEquiv
  let e₂ : AdjoinRoot (minpoly (ResidueField V) α) ≃ₐ[ResidueField V] (ResidueField V)⟮α⟯ :=
    IntermediateField.adjoinRootEquivAdjoin (ResidueField V) hint
  let e₃ : (ResidueField V)⟮α⟯ ≃ₐ[ResidueField V] k' :=
    (IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv
  let e : ResidueField (AdjoinRoot f) ≃+* k' := e₁.trans (e₂.trans e₃).toRingEquiv
  have he : ∀ v : V, e (residue (AdjoinRoot f) (algebraMap V (AdjoinRoot f) v)) =
      algebraMap (ResidueField V) k' (residue V v) := by
    intro v
    have h1 := congrArg (fun φ => φ (residue V v)) (resEquiv_comp f hf hg)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, ResidueField.map_residue] at h1
    simp only [e, e₁, RingEquiv.trans_apply, h1]
    change (e₂.trans e₃) ((AdjoinRoot.algEquivOfEq (ResidueField V) _ _ hfg)
      (algebraMap (ResidueField V) _ (residue V v))) = _
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    finite f hf, inj f hf hg, inferInstance, ?_, e, he⟩
  let eA : ResidueField (AdjoinRoot f) →ₐ[ResidueField V] k' :=
    { e.toRingHom with
      commutes' := fun c => by
        obtain ⟨v, rfl⟩ := residue_surjective c
        show e (algebraMap (ResidueField V) (ResidueField (AdjoinRoot f)) (residue V v)) = _
        rw [ResidueField.algebraMap_residue]
        exact he v }
  have : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot f)) :=
    Algebra.IsSeparable.of_algHom _ _ eA
  exact Algebra.FormallyUnramified.of_map_maximalIdeal (maxEq f hf hg).symm

end ReciprocityTheory.ChartRestriction.G.Semi.Unr
