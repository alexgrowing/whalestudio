import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbersStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UCanon

theorem torsion_sec_over_second : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := by
  intro k _ S G' _ hab G _ g₁ g₂ φ₁ φ₂ h₂ h0 hg n hn σ hσ x hx hx₁
  let T := 𝟙_ (Over (Sp (DualNumber k)))
  have hsq : ∀ y : T ⟶ G', (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g₂ := by
    intro y
    rw [Category.assoc, h₂.1.w, ← Category.assoc, Over.w y]
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ g₂) ⟶ G) := fun y => Over.homMk (y.left ≫ φ₂) (hsq y)
  have ψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    apply Over.OverMorphism.ext
    exact (h₂.2 T a b (ψ a) (ψ b) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ g₂) ⟶ G) := MonoidHom.mk' ψ ψmul
  have Ψinj : ∀ a b : T ⟶ G', Ψ a = Ψ b → a = b := by
    intro a b hab'
    apply Over.OverMorphism.ext
    exact h₂.1.hom_ext (congrArg CommaMorphism.left hab') (by rw [Over.w a, Over.w b])
  have hw : (g₂ ≫ σ.left) ≫ G.hom = 𝟙 (Sp (DualNumber k)) ≫ g₂ := by
    rw [Category.assoc, Over.w σ]; simp
  let x' : T ⟶ G' := Over.homMk (h₂.1.lift (g₂ ≫ σ.left) (𝟙 _) hw) (by simp [T])
  have hx'φ : x'.left ≫ φ₂ = g₂ ≫ σ.left := h₂.1.lift_fst _ _ _
  let u : Over.mk (T.hom ≫ g₂) ⟶ 𝟙_ (Over S) := toUnit _
  have hu : u.left = g₂ := by
    have := Over.w u
    simpa [T] using this
  have hΨx' : Ψ x' = u ≫ σ := by
    apply Over.OverMorphism.ext
    show x'.left ≫ φ₂ = u.left ≫ σ.left
    rw [hx'φ, hu]
  have hpow : ∀ m : ℕ, u ≫ σ ^ m = (u ≫ σ) ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have hx'n : x' ^ n = 1 := by
    apply Ψinj
    rw [map_pow, map_one, hΨx', ← hpow, hσ, MonObj.comp_one]
  have hb : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left := by
    apply h₂.1.hom_ext
    · have h1 := h0 (Sp k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left) (𝟙 _)
        (by rw [Category.assoc, Over.w x]; simp [T])
      rw [← h1, Category.assoc, Category.assoc, hx₁, ← Category.assoc, hg, Category.assoc, hx'φ]
    · rw [Category.assoc, Category.assoc, Over.w x, Over.w x']
  have key := GlobalTheory.T.eq_of_nsmul_eq_of_eq_closedPoint_dualNumbers k G' hab n hn x x' (by rw [hx, hx'n]) hb
  rw [key]
  exact hx'φ

end GlobalTheory.UCanon
