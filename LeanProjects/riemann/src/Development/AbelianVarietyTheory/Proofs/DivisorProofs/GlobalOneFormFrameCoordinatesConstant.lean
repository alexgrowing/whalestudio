import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem frame_coord : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R),
      (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧
        ∀ w, w = ∑ i, l i w • Φ.w i := by
  intro R _ C _ F hF n Φ
  have hd : ∀ i (w : Glob1 F), d0 F (fun T ↦ Φ.δ i T (w.1 T)) = 0 := by
    intro i w
    funext T T' φ
    rw [amitsur_d0_apply, w.2 φ, Φ.nat]
    exact sub_self _
  let c : Fin n → Glob1 F → R := fun i w ↦ (hF _ (hd i w)).exists.choose
  have hc : ∀ i w T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (c i w) :=
    fun i w ↦ (hF _ (hd i w)).exists.choose_spec
  have uniq : ∀ i w (r : R), (∀ T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) r) → c i w = r :=
    fun i w r hr ↦ (hF _ (hd i w)).unique (hc i w) hr
  refine ⟨fun i ↦
    { toFun := c i
      map_add' := fun w w' ↦ uniq i (w + w') _ (fun T ↦ by
        rw [Submodule.coe_add, Pi.add_apply, map_add, hc, hc, map_add])
      map_smul' := fun r w ↦ uniq i (r • w) _ (fun T ↦ by
        rw [Submodule.coe_smul, Pi.smul_apply, ← algebraMap_smul (F.obj T) r (w.1 T), map_smul, hc,
          RingHom.id_apply, smul_eq_mul, smul_eq_mul, map_mul]) },
    fun i w T ↦ hc i w T, fun w ↦ ?_⟩
  apply Subtype.ext
  funext T
  rw [Submodule.coe_sum, Finset.sum_apply]
  conv_lhs => rw [Φ.sum T (w.1 T)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hc, Submodule.coe_smul, Pi.smul_apply, algebraMap_smul]
  rfl

end GlobalTheory.AbCoh
