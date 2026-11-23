import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

namespace UpperTheory.AdditiveHomTwist

universe v₁ v₂ u₁ u₂

private theorem biprod_iso {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (S₁ S₂ : C) [HasBinaryBiproduct S₁ S₂] (T : D)
    (s₁ : F.obj S₁ ⟶ T) (p₁ : T ⟶ F.obj S₁) (s₂ : F.obj S₂ ⟶ T) (p₂ : T ⟶ F.obj S₂)
    (h₁ : s₁ ≫ p₁ = 𝟙 _) (h₂ : s₂ ≫ p₂ = 𝟙 _) (h₁₂ : s₁ ≫ p₂ = 0) (h₂₁ : s₂ ≫ p₁ = 0)
    (ht : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 _) : Nonempty (F.obj (S₁ ⊞ S₂) ≅ T) := by
  refine ⟨{ hom := F.map biprod.fst ≫ s₁ + F.map biprod.snd ≫ s₂
            inv := p₁ ≫ F.map biprod.inl + p₂ ≫ F.map biprod.inr
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₁₂, reassoc_of% h₂₁,
      zero_comp, comp_zero, add_zero, zero_add]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc, ← F.map_comp_assoc]
    simp only [biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      F.map_id, F.map_zero, Category.id_comp, zero_comp, comp_zero, add_zero, zero_add]
    exact ht

variable {B : Scheme.{0}} {q : ℕ}

private noncomputable def hm {P P' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (J : Shv (ZMod q)) : HP P' J ⟶ HP P J :=
  Functor.whiskerRight (NatTrans.op φ) _

private theorem hm_apply {P P' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (J : Shv (ZMod q)) (U : B.Etaleᵒᵖ)
    (x : P'.obj U.unop ⟶ J) : ((hm φ J).app U).hom x = φ.app U.unop ≫ x := rfl

private theorem hm_id (P : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (𝟙 P) J = 𝟙 _ := by
  unfold hm
  rw [NatTrans.op_id]
  exact Functor.whiskerRight_id' _

private theorem hm_comp {P P' P'' : B.Etale ⥤ Shv (ZMod q)} (φ : P ⟶ P') (ψ : P' ⟶ P'') (J : Shv (ZMod q)) :
    hm ψ J ≫ hm φ J = hm (φ ≫ ψ) J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change φ.app U.unop ≫ ψ.app U.unop ≫ (x : P''.obj U.unop ⟶ J) = (φ.app U.unop ≫ ψ.app U.unop) ≫ x
  exact (Category.assoc _ _ _).symm

private theorem hm_zero (P P' : B.Etale ⥤ Shv (ZMod q)) (J : Shv (ZMod q)) : hm (0 : P ⟶ P') J = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (0 : P.obj U.unop ⟶ P'.obj U.unop) ≫ (x : P'.obj U.unop ⟶ J) = 0
  exact zero_comp

private theorem hm_add {P P' : B.Etale ⥤ Shv (ZMod q)} (φ ψ : P ⟶ P') (J : Shv (ZMod q)) :
    hm (φ + ψ) J = hm φ J + hm ψ J := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  change (φ.app U.unop + ψ.app U.unop) ≫ (x : P'.obj U.unop ⟶ J) = φ.app U.unop ≫ x + ψ.app U.unop ≫ x
  exact Preadditive.add_comp _ _ _ _ _ _

private theorem transfer (S : SShv B q) [Injective S] {G : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (e : S.obj ≅ G) :
    ∃ h : Presheaf.IsSheaf (EtTop B) G, Injective (⟨G, h⟩ : SShv B q) := by
  have h : Presheaf.IsSheaf (EtTop B) G := (Presheaf.isSheaf_of_iso_iff e).1 S.cond
  refine ⟨h, ?_⟩
  have i : S ≅ (⟨G, h⟩ : SShv B q) :=
    (fullyFaithfulSheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).preimageIso e
  exact Injective.of_iso i inferInstance

end UpperTheory.AdditiveHomTwist

open UpperTheory.AdditiveHomTwist ZeroObject in
theorem UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct :
    ∀ (q : ℕ) (B : Scheme.{0}), (∀ P P' : B.Etale ⥤ Shv (ZMod q), Nonempty (P ≅ P') → Good P → Good P') ∧ (∀ P : B.Etale ⥤ Shv (ZMod q), (∀ U, IsZero (P.obj U)) → Good P) ∧ ∀ (P P₁ P₂ : B.Etale ⥤ Shv (ZMod q)) (i₁ : P₁ ⟶ P) (r₁ : P ⟶ P₁) (i₂ : P₂ ⟶ P) (r₂ : P ⟶ P₂), i₁ ≫ r₁ = 𝟙 _ → i₂ ≫ r₂ = 𝟙 _ → i₁ ≫ r₂ = 0 → i₂ ≫ r₁ = 0 → r₁ ≫ i₁ + r₂ ≫ i₂ = 𝟙 _ → Good P₁ → Good P₂ → Good P := by
  intro q B
  refine ⟨?_, ?_, ?_⟩
  · intro P P' hPP hP
    obtain ⟨e⟩ := hPP
    unfold Good at hP ⊢
    intro J hJ
    obtain ⟨h, hi⟩ := hP J hJ
    have e' : HP P J ≅ HP P' J :=
      { hom := hm e.inv J
        inv := hm e.hom J
        hom_inv_id := by rw [hm_comp, e.hom_inv_id, hm_id]
        inv_hom_id := by rw [hm_comp, e.inv_hom_id, hm_id] }
    exact transfer (⟨HP P J, h⟩ : SShv B q) e'
  · intro P hP
    unfold Good
    intro J hJ
    have hz : IsZero (HP P J) := by
      rw [IsZero.iff_id_eq_zero]
      have h0 : (𝟙 P : P ⟶ P) = 0 :=
        NatTrans.ext (funext fun U => (hP U).eq_of_src _ _)
      rw [← hm_id, h0, hm_zero]
    have hz0 : IsZero ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
        (0 : SShv B q)) :=
      Functor.map_isZero _ (isZero_zero _)
    exact transfer (0 : SShv B q) (hz0.iso hz)
  · intro P P₁ P₂ i₁ r₁ i₂ r₂ h1 h2 h12 h21 ht hP₁ hP₂
    unfold Good at hP₁ hP₂ ⊢
    intro J hJ
    obtain ⟨g₁, hi₁⟩ := hP₁ J hJ
    obtain ⟨g₂, hi₂⟩ := hP₂ J hJ
    let S₁ : SShv B q := ⟨HP P₁ J, g₁⟩
    let S₂ : SShv B q := ⟨HP P₂ J, g₂⟩
    haveI : Injective S₁ := hi₁
    haveI : Injective S₂ := hi₂
    obtain ⟨e⟩ := biprod_iso (sheafToPresheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))))
      S₁ S₂ (HP P J) (hm r₁ J) (hm i₁ J) (hm r₂ J) (hm i₂ J)
      (by rw [hm_comp, h1, hm_id]; rfl) (by rw [hm_comp, h2, hm_id]; rfl)
      (by rw [hm_comp, h21, hm_zero]) (by rw [hm_comp, h12, hm_zero])
      (by rw [hm_comp, hm_comp, ← hm_add, ht, hm_id])
    exact transfer (S₁ ⊞ S₂) e
