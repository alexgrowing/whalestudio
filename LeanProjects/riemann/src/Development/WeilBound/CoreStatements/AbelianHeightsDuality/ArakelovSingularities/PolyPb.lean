import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyDef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

def sumTensEquiv (σ τ : Type) : MvPolynomial (τ ⊕ σ) k ≃+* MvPolynomial σ k ⊗[k] MvPolynomial τ k :=
  (MvPolynomial.sumAlgEquiv k τ σ).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv k (MvPolynomial σ k)).symm.toRingEquiv

theorem sumTensEquiv_C (σ τ : Type) (r : k) :
    sumTensEquiv σ τ (MvPolynomial.C r) = algebraMap k (MvPolynomial σ k ⊗[k] MvPolynomial τ k) r := by
  have h1 : (MvPolynomial.sumAlgEquiv k τ σ) (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  have h2 : (MvPolynomial.C (MvPolynomial.C r) : MvPolynomial τ (MvPolynomial σ k)) =
      MvPolynomial.monomial 0 (MvPolynomial.C r) := rfl
  show (MvPolynomial.algebraTensorAlgEquiv k (MvPolynomial σ k)).symm
    ((MvPolynomial.sumAlgEquiv k τ σ) (MvPolynomial.C r)) = _
  rw [h1, h2, MvPolynomial.algebraTensorAlgEquiv_symm_monomial, Algebra.TensorProduct.algebraMap_apply]
  rfl

variable {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) {σ τ : Type}

def prodChart (e : Sp (MvPolynomial σ k) ⟶ X) (e' : Sp (MvPolynomial τ k) ⟶ Y)
    (he : e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k))
    (he' : e' ≫ g = spMap (MvPolynomial.C : k →+* MvPolynomial τ k)) :
    Sp (MvPolynomial (τ ⊕ σ) k) ⟶ pullback f g :=
  spMap (sumTensEquiv σ τ).symm.toRingHom ≫ (pullbackSpecIso k (MvPolynomial σ k) (MvPolynomial τ k)).inv ≫
    pullback.map _ _ f g e e' (𝟙 _) (by rw [Category.comp_id, he]; rfl) (by rw [Category.comp_id, he']; rfl)

variable {f g} {e : Sp (MvPolynomial σ k) ⟶ X} {e' : Sp (MvPolynomial τ k) ⟶ Y}
  {he : e ≫ f = spMap (MvPolynomial.C : k →+* MvPolynomial σ k)}
  {he' : e' ≫ g = spMap (MvPolynomial.C : k →+* MvPolynomial τ k)}

theorem isOpenImmersion_prodChart [IsOpenImmersion e] [IsOpenImmersion e'] :
    IsOpenImmersion (prodChart f g e e' he he') := by
  unfold prodChart
  have : IsIso (CommRingCat.ofHom (sumTensEquiv (k := k) σ τ).symm.toRingHom) :=
    (sumTensEquiv (k := k) σ τ).symm.toCommRingCatIso.isIso_hom
  have : IsIso (spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom) := inferInstanceAs (IsIso (Spec.map _))
  have : IsOpenImmersion (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial τ k)))) f g e e' (𝟙 _)
      (by rw [Category.comp_id, he]; rfl) (by rw [Category.comp_id, he']; rfl)) :=
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  infer_instance

theorem prodChart_str : prodChart f g e e' he he' ≫ (pullback.fst f g ≫ f) =
    spMap (MvPolynomial.C : k →+* MvPolynomial (τ ⊕ σ) k) := by
  unfold prodChart
  rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, Category.assoc, he,
    pullbackSpecIso_inv_fst_assoc]
  unfold spMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext1
  refine RingHom.ext fun r => ?_
  change (sumTensEquiv (k := k) σ τ).symm (Algebra.TensorProduct.includeLeftRingHom (MvPolynomial.C r)) = MvPolynomial.C r
  rw [RingEquiv.symm_apply_eq, sumTensEquiv_C]
  rfl

theorem range_prodChart : Set.range (prodChart f g e e' he he') =
    pullback.fst f g ⁻¹' Set.range e ∩ pullback.snd f g ⁻¹' Set.range e' := by
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial σ k))) ≫ 𝟙 (Sp k) = e ≫ f := by
    rw [Category.comp_id, he]; rfl
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial τ k))) ≫ 𝟙 (Sp k) = e' ≫ g := by
    rw [Category.comp_id, he']; rfl
  have hr := Scheme.Pullback.range_map _ _ f g e e' (𝟙 _) e₁ e₂
  have : IsIso (CommRingCat.ofHom (sumTensEquiv (k := k) σ τ).symm.toRingHom) :=
    (sumTensEquiv (k := k) σ τ).symm.toCommRingCatIso.isIso_hom
  have : IsIso (spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom) := inferInstanceAs (IsIso (Spec.map _))
  let a := spMap (sumTensEquiv (k := k) σ τ).symm.toRingHom ≫
    (pullbackSpecIso k (MvPolynomial σ k) (MvPolynomial τ k)).inv
  have ha : Function.Surjective a := (inferInstance : Surjective a).surj
  have hc : prodChart f g e e' he he' = a ≫ pullback.map _ _ f g e e' (𝟙 _) e₁ e₂ := by
    simp only [prodChart, a, Category.assoc]
  rw [hc, ← hr]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a t, (Scheme.Hom.comp_apply a _ t).symm⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨t, rfl⟩ := ha u
    exact ⟨t, Scheme.Hom.comp_apply a _ t⟩

theorem polyCovered_pullback' {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) := by
  obtain ⟨ξ, hξ, hX⟩ := hf
  obtain ⟨η, hη, hY⟩ := hg
  have heq : f ξ = g η := ((hξ (g η)).antisymm (hη (f ξ))).eq
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback ξ η heq
  refine ⟨z, fun y => ?_, fun x => ?_⟩
  · rw [Scheme.Hom.comp_apply, hz1]
    exact hξ y
  · obtain ⟨σ, _, e, he1, he2, he3, hxe, hξe⟩ := hX (pullback.fst f g x)
    obtain ⟨τ, _, e', he1', he2', he3', hxe', hηe'⟩ := hY (pullback.snd f g x)
    refine ⟨τ ⊕ σ, inferInstance, prodChart f g e e' he3 he3', isOpenImmersion_prodChart, ?_, prodChart_str, ?_, ?_⟩
    · rw [Fintype.card_sum, he2, he2', add_comm]
    · rw [range_prodChart]
      exact ⟨hxe, hxe'⟩
    · rw [range_prodChart]
      refine ⟨?_, ?_⟩
      · show pullback.fst f g z ∈ Set.range e
        rw [hz1]; exact hξe
      · show pullback.snd f g z ∈ Set.range e'
        rw [hz2]; exact hηe'

end GlobalTheory.Amb
