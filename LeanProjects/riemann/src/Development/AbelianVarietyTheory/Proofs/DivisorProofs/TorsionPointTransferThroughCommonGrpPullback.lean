import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtTrans

theorem ptTrans : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  intro V V' _ _ _ _ K _ _ _ A A' P₀ a a' h h' m x hx
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let e : TFK (R := V) K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V) K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let e' : TFK (R := V') K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V') K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let Φ : (T ⟶ P₀.A) →* (TFK (R := V) K ⟶ A.A) := (preHom e).comp (pushHom h T)
  let Φ' : (T ⟶ P₀.A) →* (TFK (R := V') K ⟶ A'.A) := (preHom e').comp (pushHom h' T)
  have hΦ : ∀ u : T ⟶ P₀.A, (Φ u).left = u.left ≫ a := fun u => by
    simp [Φ, e, preHom, pushHom, pushPt]
  have hΦ' : ∀ u : T ⟶ P₀.A, (Φ' u).left = u.left ≫ a' := fun u => by
    simp [Φ', e', preHom, pushHom, pushPt]
  have inj : Function.Injective Φ := fun u v huv => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← hΦ, ← hΦ, huv]
    · rw [Over.w u, Over.w v]
  have hsq : x.left ≫ A.A.hom = 𝟙 (Sp K) ≫ spMap (algebraMap (FractionRing V) K) := by
    rw [Over.w x, Category.id_comp]; rfl
  let w : T ⟶ P₀.A := Over.homMk (h.1.lift x.left (𝟙 _) hsq) (by simp [T])
  have hw : Φ w = x := by
    apply Over.OverMorphism.ext
    rw [hΦ]
    simp [w]
  have hwm : w ^ m = 1 := by
    apply inj
    rw [map_pow, hw, hx, map_one]
  refine ⟨w.left, Φ' w, ?_, ?_, ?_, ?_⟩
  · simpa [T] using Over.w w
  · rw [← hΦ, hw]
  · rw [hΦ']
  · rw [← map_pow, hwm, map_one]

end GlobalTheory.PtTrans
