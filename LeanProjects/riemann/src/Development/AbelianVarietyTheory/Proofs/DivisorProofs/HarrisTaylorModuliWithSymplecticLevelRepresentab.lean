import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def IsLevelStructureOfLevel {D : Datum F} {p N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (N₁ : ℕ)
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ a c, α (a + c) = α a * α c) ∧ (∀ a, α (N₁ • a) = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ a, toUnit (Over.mk x) ≫ α a = 1 ↔ ∃ b, a = N₁ • b) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ N₁ = 1 → ∃ a, toUnit _ ≫ α a = g) ∧
      ∃ z : kˣ, IsPrimitiveRoot z N₁ ∧
        ∀ a b, Out.WeilIs o.A o.PP.L N₁ (toUnit (Over.mk x) ≫ α a) (toUnit _ ≫ α b) (unitOn (z ^ D.EF a b))

def LevelStructurePullback {D : Datum F} {p N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} {s' : S' ⟶ Sp (D.OEp p)}
    {o' : Obj D p N s'} {o : Obj D p N s} {f : S' ⟶ S} (m : ObjMap o' o f) (α' : D.La → (𝟙_ (Over S') ⟶ o'.A))
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  ∀ a, (α' a).left ≫ m.φ = f ≫ (α a).left

def HasLevelStructureOfLevel {D : Datum F} {p N : ℕ} {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp (D.OEp p)} (o₁ : Obj D p N s₁) (N₁ : ℕ)
    (α₁ : D.La → (𝟙_ (Over X₁) ⟶ o₁.A)) : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : Obj D p N s) (α : D.La → (𝟙_ (Over S) ⟶ o.A)), IsLevelStructureOfLevel o N₁ α →
    ∃! f : S ⟶ X₁, f ≫ s₁ = s ∧ ∃ m : ObjMap o o₁ f, LevelStructurePullback m α α₁

abbrev LaMod (D : Datum F) (N₁ : ℕ) : Type := ZMod N₁ ⊗[ℤ] D.La

abbrev EFMod (D : Datum F) (N₁ : ℕ) : LinearMap.BilinForm (ZMod N₁) (LaMod D N₁) := D.EF.baseChange (ZMod N₁)

def toLaMod (D : Datum F) (N₁ : ℕ) : D.La →+ LaMod D N₁ :=
  (TensorProduct.mk ℤ (ZMod N₁) D.La 1).toAddMonoidHom

theorem toLaMod_apply (D : Datum F) (N₁ : ℕ) (a : D.La) : toLaMod D N₁ a = (1 : ZMod N₁) ⊗ₜ a := rfl

theorem toLaMod_surjective (D : Datum F) (N₁ : ℕ) : Function.Surjective (toLaMod D N₁) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul r a =>
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨n • a, ?_⟩
    rw [toLaMod_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

def simGrp (D : Datum F) (N₁ : ℕ) : Subgroup (LaMod D N₁ ≃ₗ[ZMod N₁] LaMod D N₁) where
  carrier := {g | ∃ m : (ZMod N₁)ˣ, ∀ x y, EFMod D N₁ (g x) (g y) = m * EFMod D N₁ x y}
  one_mem' := ⟨1, fun x y => by simp⟩
  mul_mem' := by
    rintro g h ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m * m', fun x y => ?_⟩
    change EFMod D N₁ (g (h x)) (g (h y)) = _
    rw [hm, hm', Units.val_mul, _root_.mul_assoc]
  inv_mem' := by
    rintro g ⟨m, hm⟩
    refine ⟨m⁻¹, fun x y => ?_⟩
    have h := hm (g⁻¹ x) (g⁻¹ y)
    have e : ∀ z, g (g⁻¹ z) = z := fun z => by
      change (g * g⁻¹) z = z
      rw [mul_inv_cancel]; rfl
    rw [e, e] at h
    rw [h, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

def twist (D : Datum F) (N₁ : ℕ) {T : Type} (g : simGrp D N₁) (α : D.La → T) : D.La → T :=
  fun a => α (Function.surjInv (toLaMod_surjective D N₁) ((g : LaMod D N₁ ≃ₗ[ZMod N₁] LaMod D N₁) (toLaMod D N₁ a)))

end GlobalTheory.UPel
