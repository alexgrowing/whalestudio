import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenSmoothSchemeIsSpecSmoothAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningPreimageEqClosedImmersionPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningOpenImmersionPullbackSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSurjectiveKerOfAffinePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_invariant_maps_of_affine_open : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R'] (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → (∀ σ, spMap (actC σ : C' →+* C') ≫ j = j ≫ act σ) → ∀ W : Y.left.Opens, IsAffineOpen W → φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ j.opensRange → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), Algebra.Smooth R O ∧ (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) := by
  intro R _ R' _ _ _ G' act Y φ hsm hpb hcomp hact C' _ _ _ _ actC j _ hj hjσ W hW h0
  obtain ⟨O, _, _, k, _, hkW, hkY, hOsm⟩ := GlobalTheory.T.affineOpen_smoothScheme_isSpec_smoothAlgebra R Y hsm W hW
  have hopen := GlobalTheory.T.thickening_preimage_eq_closedImmersion_preimage R' (maximalIdeal R') G' Y.left φ hcomp j.opensRange W h0
  have hB := fun e => GlobalTheory.T.thickening_open_immersion_pullback_square R' (maximalIdeal R') G' C' j hj e
  choose je hjeo hjer hjep hjeh using hB
  have hi : ∀ e, ∃ i : O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'),
      spMap (i : O →+* _) ≫ k = je e ≫ φ e := by
    intro e
    have hr : Set.range (je e ≫ φ e) ⊆ Set.range k := by
      rintro _ ⟨z, rfl⟩
      have h1 : je e z ∈ (je e).opensRange := ⟨z, rfl⟩
      rw [hjer, ← hopen, ← hkW] at h1
      exact h1
    obtain ⟨f, hf⟩ := Spec.map_surjective (IsOpenImmersion.lift k (je e ≫ φ e) hr)
    have hf' : Spec.map f ≫ k = je e ≫ φ e := by rw [hf]; exact IsOpenImmersion.lift_fac _ _ _
    have hc : CommRingCat.ofHom (algebraMap R O) ≫ f =
        CommRingCat.ofHom (algebraMap R (C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))) := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change Spec.map f ≫ spMap (algebraMap R O) = _
      rw [← hkY, ← Category.assoc, hf', Category.assoc, (hpb e).w, ← Category.assoc, hjeh]
      simp only [thick, spMap, ← Spec.map_comp]
      congr 1
      ext r
      simp [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply R R' C', Ideal.Quotient.algebraMap_eq]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    refine ⟨{ f.hom with commutes' := fun r => congrArg (fun g => g.hom r) hc }, ?_⟩
    exact hf'
  choose i hi using hi
  refine ⟨O, inferInstance, inferInstance, i, hOsm, ?_, ?_, ?_⟩
  · intro e x y hxy
    have hle : (maximalIdeal R' ^ (e + 1 + 1)).map (algebraMap R' C') ≤
        (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C') :=
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
    have hsq : spMap (Ideal.Quotient.factor hle) ≫ je (e + 1) = je e ≫ thickMap R' (maximalIdeal R') e G' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, thickMap, pullback.map, pullback.lift_fst, Category.comp_id]
        rw [(hjep (e + 1)).w, (hjep e).w, ← Category.assoc]
        congr 1
        simp only [spMap, ← Spec.map_comp]
        congr 1
      · have h1 := hjeh (e + 1)
        have h2 := hjeh e
        simp only [thickObj, Over.pullback_obj_hom] at h1 h2
        simp only [Category.assoc, thickMap, pullback.map, pullback.lift_snd]
        rw [h1, ← Category.assoc, h2]
        simp only [spMap, thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext z
        simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
    have hsp : spMap (i e : O →+* _) = spMap ((Ideal.Quotient.factor hle).comp (i (e + 1) : O →+* _)) := by
      rw [← cancel_mono k, hi, ← hcomp e, ← Category.assoc, ← hsq, Category.assoc, ← hi]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hr := congrArg (fun g => g.hom x) (Spec.map_injective hsp)
    simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hr
    have hr' : i e x = Ideal.Quotient.factor hle (i (e + 1) x) := hr
    rw [hr', ← hxy, Ideal.Quotient.factor_mk]
  · intro e σ x y hxy
    obtain ⟨h, hh1, hh2⟩ := hact e σ
    have w : (je e ≫ h) ≫ pullback.fst G'.hom (thick R' (maximalIdeal R') e) =
        (spMap (Ideal.Quotient.mk ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))) ≫
          spMap (actC σ : C' →+* C')) ≫ j := by
      rw [Category.assoc, hh1, ← Category.assoc, (hjep e).w, Category.assoc, Category.assoc, hjσ]
    have hκ1 := (hjep e).lift_fst _ _ w
    have hκ2 := (hjep e).lift_snd _ _ w
    have hκi : (hjep e).lift _ _ w ≫ spMap (i e : O →+* _) = spMap (i e : O →+* _) := by
      rw [← cancel_mono k, Category.assoc, hi, ← Category.assoc, hκ1, Category.assoc, hh2]
    obtain ⟨κ', hκ'⟩ := Spec.map_surjective ((hjep e).lift _ _ w)
    rw [← hκ'] at hκ2 hκi
    simp only [spMap, ← Spec.map_comp] at hκ2 hκi
    have r1 := congrArg (fun g => g.hom y) (Spec.map_injective hκ2)
    have r2 := congrArg (fun g => g.hom x) (Spec.map_injective hκi)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at r1 r2
    have r1' : κ'.hom (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (actC σ y) := r1
    have r2' : κ'.hom (i e x) = i e x := r2
    rw [← hxy] at r2' ⊢
    rw [← r1', r2']
  · intro e
    have hpbO : IsPullback (spMap (i e : O →+* _)) (je e) k (φ e) :=
      IsOpenImmersion.isPullback _ _ _ _ (hi e).symm (by rw [hkW, hopen, hjer])
    have hp2 := hpbO.paste_vert (hpb e)
    rw [hjeh, hkY] at hp2
    have hthick : thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R') =
        spMap (algebraMap R (R' ⧸ maximalIdeal R' ^ (e + 1))) := by
      simp only [thick, spMap, ← Spec.map_comp]
      rfl
    rw [hthick] at hp2
    let b : R' ⧸ maximalIdeal R' ^ (e + 1) →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C') :=
      { Ideal.quotientMap ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C')
          Ideal.le_comap_map with
        commutes' := fun r => by
          simp [Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_apply R R' C']
          exact (IsScalarTower.algebraMap_apply _ _ _ _).symm }
    have hb : (Ideal.Quotient.mkₐ R ((maximalIdeal R' ^ (e + 1)).map (algebraMap R' C'))).comp
        (IsScalarTower.toAlgHom R R' C') = b.comp (Ideal.Quotient.mkₐ R _) := by
      ext r
      simp [b, Ideal.quotientMap_mk]
    rw [hb]
    exact GlobalTheory.T.tensorProduct_surjective_ker_of_affine_pullback (maximalIdeal R' ^ (e + 1)) (i e) b hp2

end GlobalTheory.Mum
