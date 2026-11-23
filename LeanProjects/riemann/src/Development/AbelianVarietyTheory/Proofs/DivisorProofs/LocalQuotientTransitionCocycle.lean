import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cocycle_local_quotient_transition : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  intro S 𝒰 A H _ _ i B q b hfl hsu hqc hb hchar j k l T x y z hxy hxz
  let κ : pullback (x ≫ pullback.fst _ _) (q j).left ⟶ T := pullback.fst _ _
  let α : pullback (x ≫ pullback.fst _ _) (q j).left ⟶ pullback A.hom (𝒰.f j) := pullback.snd _ _
  have hκα : κ ≫ x ≫ pullback.fst _ _ = α ≫ (q j).left := by
    simpa [κ, α, Category.assoc] using pullback.condition (f := x ≫ pullback.fst _ _) (g := (q j).left)
  haveI : Flat κ := by dsimp [κ]; infer_instance
  haveI : Surjective κ := by dsimp [κ]; infer_instance
  haveI : QuasiCompact κ := by dsimp [κ]; infer_instance
  haveI : Epi κ := Flat.epi_of_flat_of_surjective _
  have hqj : (q j).left ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := by
    simpa using Over.w (q j)
  have ha : (α ≫ pullback.fst _ _) ≫ A.hom = κ ≫ x ≫ pullback.fst _ _ ≫ (B j).hom ≫ 𝒰.f j := by
    simp only [Category.assoc]
    rw [pullback.condition, ← reassoc_of% hqj, ← reassoc_of% hκα]
  have hak : (α ≫ pullback.fst _ _) ≫ A.hom = (κ ≫ x ≫ pullback.snd _ _) ≫ 𝒰.f k := by
    rw [ha]; simp only [Category.assoc, pullback.condition]
  have hyz : y ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ := by
    rw [← cancel_mono (𝒰.f l)]
    simp only [Category.assoc]
    rw [← pullback.condition, ← pullback.condition, ← reassoc_of% hxy, reassoc_of% (hb j k),
      ← pullback.condition, ← reassoc_of% hxz]
  have hal : (α ≫ pullback.fst _ _) ≫ A.hom = (κ ≫ z ≫ pullback.snd _ _) ≫ 𝒰.f l := by
    rw [ha]; simp only [Category.assoc, ← pullback.condition]
    rw [← reassoc_of% hxz]
  have hk1 := pullback.lift_fst _ _ hak
  have hk2 := pullback.lift_snd _ _ hak
  have hl1 := pullback.lift_fst _ _ hal
  have hl2 := pullback.lift_snd _ _ hal
  have h1 := hchar j k _ α (pullback.lift _ _ hak) (κ ≫ x) hk1.symm
    (by rw [Category.assoc]; exact hκα) (by rw [hk2, Category.assoc])
  have h2 := hchar j l _ α (pullback.lift _ _ hal) (κ ≫ z) hl1.symm
    (by rw [Category.assoc, ← hxz]; exact hκα) (by rw [hl2, Category.assoc])
  have h3 := hchar k l _ (pullback.lift _ _ hak) (pullback.lift _ _ hal) (κ ≫ y) (hk1.trans hl1.symm)
    (by rw [Category.assoc, ← hxy, ← Category.assoc]; exact h1)
    (by rw [hl2, Category.assoc, hyz])
  rw [← cancel_epi κ, ← Category.assoc, h3, ← h2, Category.assoc]

end GlobalTheory
