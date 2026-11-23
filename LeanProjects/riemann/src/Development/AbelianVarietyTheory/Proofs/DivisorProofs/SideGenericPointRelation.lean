import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry.Corr.CentreOfDominating

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem spMap_closedPoint {W : Type} [CommRing W] [IsLocalRing W] {Ω : Type} [Field Ω] (r : W →+* Ω)
    (hr : RingHom.ker r = IsLocalRing.maximalIdeal W) :
    (spMap r) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint W := by
  have : IsLocalHom r := ⟨fun a ha => by
    by_contra h
    have hm : a ∈ IsLocalRing.maximalIdeal W := h
    rw [← hr, RingHom.mem_ker] at hm
    rw [hm] at ha
    exact not_isUnit_zero ha⟩
  exact IsLocalRing.comap_closedPoint r

theorem exists_common_residue {O W₁ W₂ : Type} [CommRing O] [IsLocalRing O] [CommRing W₁] [IsLocalRing W₁]
    [CommRing W₂] [IsLocalRing W₂] (ψ₁ : O →+* W₁) (ψ₂ : O →+* W₂) [IsLocalHom ψ₁] [IsLocalHom ψ₂] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (r₁ : W₁ →+* Ω) (r₂ : W₂ →+* Ω),
      RingHom.ker r₁ = IsLocalRing.maximalIdeal W₁ ∧ RingHom.ker r₂ = IsLocalRing.maximalIdeal W₂ ∧
      r₁.comp ψ₁ = r₂.comp ψ₂ := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField W₁) :=
    (IsLocalRing.ResidueField.map ψ₁).toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField W₂) :=
    (IsLocalRing.ResidueField.map ψ₂).toAlgebra
  let T := TensorProduct (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField W₁) (IsLocalRing.ResidueField W₂)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  letI := Ideal.Quotient.field m
  let c : T →+* AlgebraicClosure (T ⧸ m) :=
    (algebraMap (T ⧸ m) (AlgebraicClosure (T ⧸ m))).comp (Ideal.Quotient.mk m)
  let e₁ : IsLocalRing.ResidueField W₁ →+* AlgebraicClosure (T ⧸ m) :=
    c.comp (Algebra.TensorProduct.includeLeft : _ →ₐ[IsLocalRing.ResidueField O] T).toRingHom
  let e₂ : IsLocalRing.ResidueField W₂ →+* AlgebraicClosure (T ⧸ m) :=
    c.comp (Algebra.TensorProduct.includeRight : _ →ₐ[IsLocalRing.ResidueField O] T).toRingHom
  have hk : ∀ {W : Type} [CommRing W] [IsLocalRing W] (e : IsLocalRing.ResidueField W →+* AlgebraicClosure (T ⧸ m)),
      RingHom.ker (e.comp (IsLocalRing.residue W)) = IsLocalRing.maximalIdeal W := by
    intro W _ _ e
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff e e.injective, IsLocalRing.residue_eq_zero_iff]
  refine ⟨AlgebraicClosure (T ⧸ m), inferInstance, inferInstance, e₁.comp (IsLocalRing.residue W₁),
    e₂.comp (IsLocalRing.residue W₂), hk e₁, hk e₂, RingHom.ext fun a => ?_⟩
  simp only [RingHom.comp_apply]
  rw [← IsLocalRing.ResidueField.map_residue ψ₁, ← IsLocalRing.ResidueField.map_residue ψ₂]
  have h₁ : IsLocalRing.ResidueField.map ψ₁ (IsLocalRing.residue O a) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField W₁) (IsLocalRing.residue O a) := rfl
  have h₂ : IsLocalRing.ResidueField.map ψ₂ (IsLocalRing.residue O a) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField W₂) (IsLocalRing.residue O a) := rfl
  rw [h₁, h₂]
  simp only [e₁, e₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

end GlobalTheory.ShFam.GalCarry.Corr.CentreOfDominating

namespace GlobalTheory.ShFam.GalCarry.Corr

open CentreOfDominating in

theorem centre_eq_of_dominatesStalk : ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop), Side Y Y' Rel → ∀ (i : I) (i' : I') (p' : Sp (Y i).Fn ⟶ (Y' i').X),
      Rel (AlgebraicClosure (Y i).Fn) i i' (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i))
        (spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ p') →
      ∀ (y : (Y i).X) (W₁ W₂ : ValuationSubring (Y i).Fn) (q₁ : Sp W₁ ⟶ (Y' i').X) (q₂ : Sp W₂ ⟶ (Y' i').X),
        GlobalTheory.DominatesStalk W₁ y → GlobalTheory.DominatesStalk W₂ y → spMap (algebraMap W₁ (Y i).Fn) ≫ q₁ = p' →
        spMap (algebraMap W₂ (Y i).Fn) ≫ q₂ = p' → q₁ (IsLocalRing.closedPoint W₁) = q₂ (IsLocalRing.closedPoint W₂) := by
  intro F _ _ I I' Y Y' Rel hS i i' p' hp y W₁ W₂ q₁ q₂ hW₁ hW₂ hq₁ hq₂
  obtain ⟨-, -, h3, h4⟩ := hS
  obtain ⟨ψ₁, hψ₁, hψ₁'⟩ := GlobalTheory.dominatesStalk_iff_exists_isLocalHom.mp hW₁
  obtain ⟨ψ₂, hψ₂, hψ₂'⟩ := GlobalTheory.dominatesStalk_iff_exists_isLocalHom.mp hW₂
  obtain ⟨Ω, _, _, r₁, r₂, hk₁, hk₂, hr⟩ := exists_common_residue ψ₁ ψ₂
  have key : ∀ (W : ValuationSubring (Y i).Fn) (ψ : (Y i).X.presheaf.stalk y →+* W),
      (∀ a, (ψ a : (Y i).Fn) = algebraMap _ (Y i).Fn a) → ∀ (q : Sp W ⟶ (Y' i').X),
      spMap (algebraMap W (Y i).Fn) ≫ q = p' → ∀ (r : W →+* Ω), RingHom.ker r = IsLocalRing.maximalIdeal W →
      Rel Ω i i' (spMap (r.comp ψ) ≫ (Y i).X.fromSpecStalk y) (spMap r ≫ q) := by
    intro W ψ hψ q hq r hr
    have e1 : spMap (algebraMap W (Y i).Fn) ≫ spMap ψ ≫ (Y i).X.fromSpecStalk y = genericPt (Y i) := by
      rw [← Category.assoc, sp_comp, show (algebraMap W (Y i).Fn).comp ψ = algebraMap _ (Y i).Fn from RingHom.ext hψ]
      exact GlobalTheory.specAlgebraMap_fromSpecStalk y
    have hinj : Function.Injective ((algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)).comp (algebraMap W (Y i).Fn)) :=
      (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)).injective.comp Subtype.val_injective
    have h := h4 W (AlgebraicClosure (Y i).Fn) _ Ω r i i' (spMap ψ ≫ (Y i).X.fromSpecStalk y) q hinj hr (by
      rw [← sp_comp, Category.assoc, Category.assoc, e1, hq]
      exact hp)
    rwa [← Category.assoc, sp_comp] at h
  have R1 := key W₁ ψ₁ hψ₁' q₁ hq₁ r₁ hk₁
  have R2 := key W₂ ψ₂ hψ₂' q₂ hq₂ r₂ hk₂
  rw [← hr] at R2
  obtain ⟨s, -, hu⟩ := h3 Ω i (spMap (r₁.comp ψ₁) ≫ (Y i).X.fromSpecStalk y)
  have e := (hu ⟨i', spMap r₁ ≫ q₁⟩ R1).trans (hu ⟨i', spMap r₂ ≫ q₂⟩ R2).symm
  have e' : spMap r₁ ≫ q₁ = spMap r₂ ≫ q₂ := eq_of_heq (Sigma.mk.inj_iff.mp e).2
  calc q₁ (IsLocalRing.closedPoint W₁) = q₁ ((spMap r₁) (IsLocalRing.closedPoint Ω)) := by
        rw [spMap_closedPoint r₁ hk₁]
    _ = (spMap r₁ ≫ q₁) (IsLocalRing.closedPoint Ω) := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (spMap r₂ ≫ q₂) (IsLocalRing.closedPoint Ω) := by rw [e']
    _ = q₂ ((spMap r₂) (IsLocalRing.closedPoint Ω)) := Scheme.Hom.comp_apply _ _ _
    _ = q₂ (IsLocalRing.closedPoint W₂) := by rw [spMap_closedPoint r₂ hk₂]

end GlobalTheory.ShFam.GalCarry.Corr
