import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEigen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

variable {K : Type} [Field K]

def tors (B : AbVar K) (n : ℕ) : Subgroup (𝟙_ (Over (Sp K)) ⟶ B.X) := (powMonoidHom n).ker

theorem mem_tors {B : AbVar K} {n : ℕ} {y : 𝟙_ (Over (Sp K)) ⟶ B.X} : y ∈ tors B n ↔ y ^ n = 1 := Iff.rfl

abbrev mulN (B : AbVar K) (n : ℕ) : B.X.left ⟶ B.X.left := (𝟙 B.X ^ (n : ℤ)).left

def transl (B : AbVar K) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) : B.X ⟶ B.X := (toUnit B.X ≫ y) * 𝟙 B.X

theorem transl_mulN (B : AbVar K) (n : ℕ) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) (hy : y ∈ tors B n) :
    (transl B y).left ≫ mulN B n = mulN B n := by
  rw [mulN, ← Over.comp_left]
  congr 1
  rw [zpow_natCast, transl, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow,
    mem_tors.1 hy, MonObj.comp_one, _root_.one_mul]

theorem preimage_le (B : AbVar K) (n : ℕ) (y : 𝟙_ (Over (Sp K)) ⟶ B.X) (hy : y ∈ tors B n) (V : B.X.left.Opens) :
    mulN B n ⁻¹ᵁ V ≤ (transl B y).left ⁻¹ᵁ (mulN B n ⁻¹ᵁ V) := fun x hx => by
  change ((transl B y).left ≫ mulN B n) x ∈ V
  rw [transl_mulN B n y hy]
  exact hx

def act (B : AbVar K) (n : ℕ) (y : tors B n) (V : B.X.left.Opens) :
    Γ(B.X.left, mulN B n ⁻¹ᵁ V) →+* Γ(B.X.left, mulN B n ⁻¹ᵁ V) :=
  ((transl B y.1).left.appLE (mulN B n ⁻¹ᵁ V) (mulN B n ⁻¹ᵁ V) (preimage_le B n y.1 y.2 V)).hom

def cst (B : AbVar K) (W : B.X.left.Opens) : K →+* Γ(B.X.left, W) :=
  (B.X.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

def IsEig (B : AbVar K) (n : ℕ) (χ : tors B n →* Kˣ) (V : B.X.left.Opens) (u : Γ(B.X.left, mulN B n ⁻¹ᵁ V)ˣ) :
    Prop :=
  ∀ y : tors B n, act B n y V (u : Γ(B.X.left, mulN B n ⁻¹ᵁ V)) = cst B _ ((χ y : Kˣ) : K) * (u : Γ(B.X.left, mulN B n ⁻¹ᵁ V))

def eigen (B : AbVar K) (n : ℕ) (χ : tors B n →* Kˣ) : LB B.X.left :=
  GlobalTheory.EigenDescent.eigenLB (mulN B n) (IsEig B n χ)

end GlobalTheory.PushEigen
