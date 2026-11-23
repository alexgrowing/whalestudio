import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel.ModelOpen

theorem exists_geomIrr_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ U : (Xo'.XF c').Opens,
    (∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∃ Xw : Y.X.Opens, (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
      (∀ z, Y.j z ∈ Xw ↔ z ∈ U) ∧ GeomIrr Y.s Xw := by
  intro E _ _ _ H Dw l' Xo' c' W Y p hp hW U hU
  have hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  have := c'.fin
  have hV : (p : c'.F) ∈ (c'.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c'.F.val.toRingHom (p : c'.F)⁻¹ ∈ W := h
    simpa using h2
  have := GlobalTheory.LocM.BaseMdl.away_of_valuation c'.F (c'.V W) p hp hV
  have hβ : IsOpenImmersion (spMap (c'.V W).subtype) :=
    IsOpenImmersion.of_isLocalization (S := c'.F) ((p : ℕ) : c'.V W)
  refine ⟨Y.j ''ᵁ U, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro _ ⟨z, -, rfl⟩
    have hF : IsUnit (p : Γ(Sp c'.F, ⊤)) := by
      have h0 : IsUnit (p : c'.F) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hp.ne_zero)
      have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of c'.F)).inv.hom
      rw [map_natCast] at h1
      exact h1
    have hunit : IsUnit (p : Γ(Xo'.XF c', ⊤)) := by
      have h1 := hF.map (Scheme.Hom.appTop (pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom))).hom
      rw [map_natCast] at h1
      exact h1
    have hz : z ∈ Y.j ⁻¹ᵁ Y.X.basicOpen (p : Γ(Y.X, ⊤)) := by
      rw [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit _ hunit).ge trivial
    exact hz
  · intro z
    constructor
    · rintro ⟨z', hz', e⟩
      rwa [← Y.j.isOpenEmbedding.injective e]
    · intro hz
      exact ⟨z, hz, rfl⟩
  · intro k _ f hf
    let β := (c'.V W).subtype
    let f' : c'.F →+* k := IsFractionRing.lift hf
    have hff : f'.comp β = f := by
      ext x
      exact IsFractionRing.lift_algebraMap hf x
    let a := U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)
    have := hU k f'
    let e := Y.j.isoImage U
    have h1 : a ≫ spMap β = e.hom ≫ (Y.j ''ᵁ U).ι ≫ Y.s := by
      rw [Scheme.Hom.isoImage_hom_ι_assoc, GlobalTheory.LocM.BaseMdl.j_s]
      exact Category.assoc _ _ _
    have h2 : spMap f' ≫ spMap β = spMap f := by
      rw [← hff]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let φ := pullback.map a (spMap f') ((Y.j ''ᵁ U).ι ≫ Y.s) (spMap f) e.hom (𝟙 _) (spMap β) h1
      (by rw [h2, Category.id_comp])
    let ψ : pullback ((Y.j ''ᵁ U).ι ≫ Y.s) (spMap f) ⟶ pullback a (spMap f') :=
      pullback.lift (pullback.fst _ _ ≫ e.inv) (pullback.snd _ _) (by
        rw [← cancel_mono (spMap β)]
        simp only [Category.assoc, h1, Iso.inv_hom_id_assoc, h2]
        exact pullback.condition)
    have hφψ : ψ ≫ φ = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [φ, ψ, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id,
          Category.comp_id, Category.id_comp]
      · simp only [φ, ψ, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id, Category.id_comp]
    have hsurj : Function.Surjective φ := fun x => ⟨ψ x, by rw [← Scheme.Hom.comp_apply, hφψ]; rfl⟩
    exact hsurj.irreducibleSpace φ.continuous

end GlobalTheory.FlatModel.ModelOpen
