import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.SpreadGrp

theorem grpObj_of_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  intro R _ _ f g hf X q hq hs A _ _ i hA H h hH m n o hm hn ho
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsSchemeTheoreticallyDominant (awayMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) hinj
  have : Flat (awayMap g) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers g))
  have : Flat H.hom := MorphismProperty.of_isPullback hH hq
  have : IsSeparated H.hom := MorphismProperty.of_isPullback hH hs
  have := ExtUnique.flat_tensorUnit (S := Sp (Localization.Away g))
  have := ExtUnique.flat_tensorObj H H
  have := ExtUnique.flat_tensorObj (𝟙_ _) H
  have := ExtUnique.flat_tensorObj H (𝟙_ _)
  have := ExtUnique.flat_tensorObj (H ⊗ H) H
  let j := pullback.fst (awayMap g) (awayMap f)
  let k := pullback.snd (awayMap g) (awayMap f)
  have w : ∀ T : Over (pullback (awayMap g) (awayMap f)), (T.hom ≫ j) ≫ awayMap g = (T.hom ≫ k) ≫ awayMap f := by
    intro T; simp only [Category.assoc, j, k, pullback.condition]

  have key : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → ∀ a : Over.mk t₁ ⟶ H, ∃ a' : Over.mk t₀ ⟶ A, a.left ≫ h = a'.left ≫ i := by
    intro T t₁ t₀ e a
    have e' : (a.left ≫ h) ≫ q = t₀ ≫ awayMap f := by
      rw [Category.assoc, hH.w, ← Category.assoc, Over.w a]; exact e
    exact ⟨Over.homMk (hA.lift (a.left ≫ h) t₀ e') (hA.lift_snd _ _ _), (hA.lift_fst _ _ _).symm⟩

  have inj : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} (a b : Over.mk t₁ ⟶ H),
      a.left ≫ h = b.left ≫ h → a = b := by
    intro T t₁ a b e
    exact Over.OverMorphism.ext (hH.hom_ext e (by rw [Over.w a, Over.w b]))
  have hone : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → (toUnit (Over.mk t₁) ≫ o).left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i := by
    intro T t₁ t₀ e
    simpa using ho T t₁ t₀ e
  letI : MonObj H :=
    { one := o
      mul := m
      one_mul := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ snd _ _ = x := ⟨_, rfl⟩
        have ht : t = lift (toUnit _) x :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hone (w T)) hx', _root_.one_mul, hx']
      mul_one := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ = x := ⟨_, rfl⟩
        have ht : t = lift x (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hone (w T)), _root_.mul_one, hx']
      mul_assoc := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ ≫ fst _ _ = x := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ : ∃ y, t ≫ fst _ _ ≫ snd _ _ = y := ⟨_, rfl⟩
        obtain ⟨z, hz⟩ : ∃ z, t ≫ snd _ _ = z := ⟨_, rfl⟩
        have ht : t = lift (lift x y) z := by
          ext <;> simp [← hx, ← hy, ← hz]
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        obtain ⟨y', hy'⟩ := key (w T) y
        obtain ⟨z', hz'⟩ := key (w T) z
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hm _ _ _ _ _ _ _ hx' hy') hz', hm _ _ _ _ _ _ _ hx' (hm _ _ _ _ _ _ _ hy' hz'),
          _root_.mul_assoc] }
  letI : GrpObj H :=
    { inv := n
      left_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift n (𝟙 H) ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hn _ _ _ _ _ hx') hx', inv_mul_cancel, hone (w T)]
      right_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift (𝟙 H) n ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hn _ _ _ _ _ hx'), mul_inv_cancel, hone (w T)] }
  exact ⟨inferInstance, fun T t₁ t₂ a b a' b' ha hb => hm T t₁ t₂ a b a' b' ha hb⟩

end GlobalTheory.Desc.SpreadGrp
