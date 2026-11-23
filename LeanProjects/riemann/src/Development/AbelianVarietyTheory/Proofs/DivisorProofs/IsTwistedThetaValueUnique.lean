import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum

theorem isTwVal_unique {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)) (hN : Odd N) (H : IsTwVal P N m θ τ β x h v)
    (H' : IsTwVal P N m θ τ β x h v') : v = v' := by
  obtain ⟨α, U, hα, hU, e⟩ := H
  obtain ⟨α', U', hα', hU', e'⟩ := H'
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hc := GlobalTheory.SymLiftOdd.symLift_unique hG P.isAb P.isLB hN U U' hU hU'
  obtain ⟨c, hcv⟩ := GlobalTheory.SymLiftOdd.exists_const P.isLB (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (GlobalTheory.SymLiftOdd.surj_fst hG P.isAb T)
    (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen P.L _ _ _ _ α (LB.invGen P.L _ _ α') hα (DVR.invGen_isGen _ _ _ _ hα'))
  refine fn_ext fun y _ => ?_
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  have r : ∀ w : T ⟶ P.A, val α (𝟙 _ ≫ (ptSecT P.A w).left) y J =
      val α' (𝟙 _ ≫ (ptSecT P.A w).left) y J * gm (𝟙 T.left) y ⊤ c := fun w => by
    have k := hcv _ (𝟙 _ ≫ (ptSecT P.A w).left) y J hJ'
    have k₂ : (𝟙 _ ≫ (ptSecT P.A w).left) ≫ (fst T P.A).left = 𝟙 T.left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_fst]; rfl
    rw [k₂, val_mul hJ', val_inv] at k
    rw [← k, mul_comm, inv_mul_cancel_right]
  have t : GlobalTheory.CommPairing.tval U (𝟙 _ ≫ (ptSecT P.A h).left) y J =
      GlobalTheory.CommPairing.tval U' (𝟙 _ ≫ (ptSecT P.A h).left) y J := val_corr hJ' hc _
  have e₁ := e _ (𝟙 _) y J hJ'
  have e₂ := e' _ (𝟙 _) y J hJ'
  rw [r, r, t] at e₁
  refine (Units.mul_left_inj (val α' (𝟙 _ ≫ (ptSecT P.A h).left) y J * gm (𝟙 T.left) y ⊤ c *
    val τ (𝟙 _ ≫ β.left) y J)).1 (e₁.trans ?_)
  simp only [Units.val_mul] at e₂ ⊢
  linear_combination (-(gm (𝟙 T.left) y ⊤ c).val) * e₂

end GlobalTheory.UPoinc.USum
