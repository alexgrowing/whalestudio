import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

theorem chart_fn_mul_gen_pow : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (k : ℕ) (σ : SecM m₁ L k) (ρ : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → ∀ (p : h₁.J × (Fin 2 → L.ι)), rsT (ρ.f fun _ => p.2 0) (GlobalTheory.Heat.Gauge.W m h₁ p) = (GlobalTheory.Heat.Gauge.gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (GlobalTheory.Heat.Gauge.W m h₁ p) := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have le₀ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => p.2 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => W_le_m m h₁ p hy
  have le₁ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m₁) (fun _ => h₁.j p.1) :=
    fun y hy => Set.mem_iInter.2 fun _ => (W_le_m₁ m h₁ p hy).2
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : G.left ⟶ X => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 G.left : G.left ⟶ G.left) y ∈ W m h₁ p := hy
  have e₀ : gs (𝟙 G.left) y _ (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => p.2 0) (fun _ => J (𝟙 G.left ≫ m))).val *
        sval ρ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₀ _)).trans ((gs_res (𝟙 G.left) y le₀ hy' _).trans
      (sec_trans ρ (𝟙 G.left) y (le₀ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₁ : gs (𝟙 G.left) y _ (rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m₁) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => h₁.j p.1) (fun _ => J (𝟙 G.left ≫ m₁))).val *
        sval σ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₁ _)).trans ((gs_res (𝟙 G.left) y le₁ hy' _).trans
      (sec_trans σ (𝟙 G.left) y (le₁ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₂ : gm (𝟙 G.left) y _ (gU m h₁ e p) =
      (trF ![m, m₁] ![1, -1] (𝟙 G.left) y p.2 (fun a => J (𝟙 G.left ≫ ![m, m₁] a)) * val e (𝟙 G.left) y J) *
        gm (𝟙 G.left ≫ m₁) y _ (L.g (p.2 1) (h₁.j p.1)) :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 G.left) y (W_le_wchart m h₁ p) hy' _).trans
        (gen_trans he (𝟙 G.left) y (W_le_wchart m h₁ p hy) (hJ'.mem _ (𝟙 G.left))))
      ((gm_res (𝟙 G.left) y (W_le_m₁ m h₁ p) hy' _).trans (gm_pull (𝟙 G.left) m₁ y _ (W_le_m₁ m h₁ p hy) _)))
  have e₃ : gs (𝟙 G.left) y _ ((gU m h₁ e p).val ^ k) = (gm (𝟙 G.left) y _ (gU m h₁ e p) ^ k).val := by
    rw [← Units.val_pow_eq_pow_val, gs_unit _ _ _ hy', map_pow]
  have hc := gm_cocycle hL (𝟙 G.left ≫ m₁) y (W_le_m₁ m h₁ p hy).1 (W_le_m₁ m h₁ p hy).2 (hJ (𝟙 G.left ≫ m₁))
  rw [gs_mul _ _ _ hy', e₀, e₁, e₃, e₂, hρ _ _ y J hJ', ← _root_.mul_assoc, ← _root_.mul_assoc, mul_right_comm, ← Units.val_mul,
    ← Units.val_mul]
  congr 2
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_natCast,
    zpow_one, zpow_neg]
  rw [← mul_pow, ← mul_pow]
  congr 1
  rw [_root_.mul_assoc _ (gm _ _ _ (L.g (p.2 1) _)), hc]
  rw [mul_right_comm _ (val e _ y J)]
  exact congrArg (· * val e _ y J) (inv_mul_cancel_right _ _).symm

end GlobalTheory.Heat.Gauge
