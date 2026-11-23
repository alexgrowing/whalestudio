import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslatePullbackEigensection
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EigenEquationOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

open TopologicalSpace in

theorem exists_gen_move_back : ∀ (Y Y' X₁ X₂ W : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂), L₁.IsLB → L₂.IsLB → ∀ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → ∀ (K : Type) [Fintype K] (m : K → (Y' ⟶ Y)) (ε : K → ℤ) (φ₁ : K → (Y' ⟶ X₁)), (∀ k, φ₁ k = m k ≫ f₁) → ∀ (φ₂ : K → (W ⟶ X₂)) (h : Y' ⟶ W), (∀ k, h ≫ φ₂ k = m k ≫ f₂) → ∀ t : LB.Gen (LB.LinComb L₂ φ₂ ε), t.IsGen → ∃ a : LB.Gen (LB.LinComb L₁ φ₁ ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₂ : (Z ⟶ X₂) → L₂.ι) (J₁ : (Z ⟶ X₁) → L₁.ι), Good L₂ z J₂ → Good L₁ z J₁ → val t (r ≫ h) z J₂ = (∏ k, isoVal w (r ≫ m k) z (J₂ ((r ≫ m k) ≫ f₂)) (J₁ ((r ≫ m k) ≫ f₁)) ^ ε k) * val a r z J₁ := by
  intro Y Y' X₁ X₂ W L₁ L₂ hL₁ hL₂ f₁ f₂ w hw K _ m ε φ₁ e₁ φ₂ h hc t ht
  classical
  obtain rfl : φ₁ = fun k => m k ≫ f₁ := funext e₁
  let O : (K → L₁.ι) → (K → L₂.ι) → Y'.Opens := fun q p =>
    LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₂ (fun k => m k ≫ f₂) p
  have pt : ∀ k y, φ₂ k (h y) = f₂ (m k y) := fun k y => congrArg (fun q : Y' ⟶ X₂ => q y) (hc k)
  have le1 : ∀ q p k, O q p ≤ m k ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => p k) ⊓ (L₁.pull f₁).U (fun _ => q k)) :=
    fun q p k y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L₂ φ₂ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    show φ₂ k (h y) ∈ L₂.U (p k)
    rw [pt]; exact Set.mem_iInter.1 hy.2 k
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (m k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹ *
      res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m1 := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans
      (gm_pull r (m k) z _ m1 _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L₁ (fun k => m k ≫ f₁) q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => hp k⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L₁ (fun k => m k ≫ f₁) q)ˣ,
      ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, f₂ (m k y) ∈ L₂.U (p k) := fun k => Set.mem_iInter.1 hy.1.2 k
      have hp' : ∀ k, f₂ (m k y) ∈ L₂.U (p' k) := fun k => Set.mem_iInter.1 hy.2.2 k
      have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
          gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) * isoVal w (𝟙 Y' ≫ m k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp' k) (hq k) (hq k),
          gm_self hL₁ (m k ≫ f₁) y (hq k), inv_one, _root_.mul_one]
      have e2 : trF φ₂ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [_root_.mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z J₂ J₁ hJ₂ hJ₁ => ?_⟩
  · have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, f₁ (m k y) ∈ L₁.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    have m0 : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => hp k⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => hp k⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
      gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₁ (fun k => m k ≫ f₁) q')
      ((LB.LinComb L₁ (fun k => m k ≫ f₁) ε).g q q') * gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q') (s q')
    rw [gm_linComb L₁ (fun k => m k ≫ f₁) ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m0, vals _ _ y q' p m']
    have e3 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ m k ≫ f₁) y _ (L₁.g (q k) (q' k)))⁻¹ * isoVal w (𝟙 Y' ≫ m k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, Category.id_comp,
        GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp k) (hq k) (hq' k),
        gm_self hL₂ (m k ≫ f₂) y (hp k), _root_.one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (_root_.mul_assoc _ _ _)
  · have m0 : r z ∈ O (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => J₂ ((r ≫ m k) ≫ f₂)) :=
      ⟨Set.mem_iInter.2 fun k => hJ₁ ((r ≫ m k) ≫ f₁), Set.mem_iInter.2 fun k => hJ₂ ((r ≫ m k) ≫ f₂)⟩
    rw [val_of t (r ≫ h) z J₂ (fun k => J₂ ((r ≫ m k) ≫ f₂))
        (fun k => by rw [Category.assoc, hc k, Category.assoc]),
      val_of _ r z J₁ (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => by rw [Category.assoc])]
    show _ = _ * gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) _) (s _)
    rw [vals Z r z _ _ m0, mul_inv_cancel_left]

end GlobalTheory.Jets
