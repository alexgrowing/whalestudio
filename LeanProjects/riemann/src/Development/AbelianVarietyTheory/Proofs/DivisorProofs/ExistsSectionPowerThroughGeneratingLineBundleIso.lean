import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdScalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenGeneric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecThroughIso

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_sec_of_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k),
    ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j →
        gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k *
          gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h₁ h₂ k σ'
  let t : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))) :=
    TG.pullSec' L₁ (fun _ => 𝟙 X₁) (fun _ => (k : ℤ)) σ' f₁ (fun _ => f₁) (fun _ => (Category.comp_id _).symm)
  refine ⟨secOfIso (u := flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _), ?_⟩
  intro y i j hi hj
  have hz : (𝟙 Y) y ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e := ps_gs_secOfIso (flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _)
    (fun _ => i) (fun _ => j) (𝟙 Y) y hz
  have hw' : (𝟙 Y) y ∈ ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e1 : gm (𝟙 Y) y _ ((flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))).s (fun _ => j, fun _ => i)) =
      gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ)) := by
    show gm (𝟙 Y) y _ (∏ k' : Fin 1, res (flat_le L₁ L₂ f₁ f₂ (fun _ => j, fun _ => i) k')
      (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ))) = _
    rw [map_prod, Fin.prod_univ_one, map_zpow]
    congr 1
    exact gm_res _ y _ (show (𝟙 Y) y ∈ LB.wchart L₁ (fun _ : Fin 1 => f₁) (fun _ => j) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) from ⟨hz.2, hz.1⟩) _
  have e2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs f₁ y _ (σ'.f fun _ => j) := by
    simp only [t]
    rw [TG.pullSec'_f]
    refine (gs_res _ y _ hz.2 _).trans ?_
    refine (gs_pull (𝟙 Y) f₁ y _ (Set.mem_iInter.2 fun _ => hj) _).trans ?_
    rw [Category.id_comp]
    rfl
  rw [e, e1, e2, gs_unit _ y _ hw', zpow_neg, inv_inv, zpow_natCast, Units.val_pow_eq_pow_val]

end GlobalTheory.SecThroughIso
