import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OperatorPoint

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem trPt_inv_comp (b : TF (R := R) F ⟶ D.P.A) : DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
  · have e : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact e.trans (Category.id_comp _).symm

theorem phiVal_inv {n : ℕ} (p : QkPt D F n)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)))
    {s t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε n))} (h : PhiVal p w s t)
    (α β : D.X) (hβ : α + p.y = β) (b : TF (R := R) F ⟶ D.P.A) (hb : p.g.b = b) (y : (DegPre.BF D F).left) (J)
    (hJ : Good D.P.L y J) :
    sval (t β) (DegPre.trPt D F b⁻¹).left y J = sval (s α) (𝟙 _) y J *
      (uVal D F n α b (DegPre.trPt D F b⁻¹) y J * (val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J *
        val w (fst (TF (R := R) F) D.P.A).left y J)).val := by
  subst hb
  have e := h α β hβ _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [trPt_inv_comp, tr_fst, val_mul hJ] at e
  exact e

end OperatorPoint

open ReciprocityTheory.ChartRestriction.G.DVR OperatorPoint in

theorem qkPt_g_eq_of_phiRel :
    GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b → p.g = p'.g := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy hb
  have hI := (degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F).1
  have key : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w (fst (TF (R := R) F) D.P.A).left y J =
        val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J * val w' (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D) (F := F) hT hn α
    obtain ⟨s, rfl, -⟩ := FamFree.exists_fam_single hG hB hn α σ
    obtain ⟨t, h₁, h₂⟩ := H s
    have e₁ := phiVal_inv p w ((phiRel_iff hG p w hw s t).1 h₁) α (α + p.y) rfl _ rfl y J hJ
    have e₂ := phiVal_inv p' w' ((phiRel_iff hG p' w' hw' s t).1 h₂) α (α + p.y) (by rw [hy]) _ hb.symm y J hJ
    have hne : sval (s.s α) (𝟙 _) y J ≠ 0 :=
      RootUnit.sec_gs_ne_zero (s.s α) (not_forall.1 hσ) y _ (hJ.mem _ (𝟙 _))
    exact mul_left_cancel (Units.ext (mul_left_cancel₀ hne (e₁.symm.trans e₂)))
  have key' : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      val (p.g.s α) (fst (TF (R := R) F) D.P.A).left y J = val (p'.g.s α) (fst (TF (R := R) F) D.P.A).left y J := by
    intro α y J hJ
    have e₀ := key 0 y J hJ
    rw [val_corr hJ p.g.s_zero, val_corr hJ p'.g.s_zero, val_one, _root_.one_mul, _root_.one_mul] at e₀
    have e := key α y J hJ
    rw [e₀] at e
    exact mul_right_cancel e
  refine TorusExt.gt_ext hb fun χ => corr_of_val D.P.isLB fun y J hJ => ?_
  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (p.g.s χ) (fst (TF (R := R) F) D.P.A).left)
      (LB.pullGen D.P.L _ _ (p'.g.s χ) (fst (TF (R := R) F) D.P.A).left) :=
    corr_of_val D.P.isLB fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, Category.id_comp]; exact key' χ y J hJ
  have z₁ : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _)
  have e := val_corr hJ hc (DegPre.zF D F).left
  rwa [val_pull hJ, val_pull hJ, z₁] at e

end GlobalTheory
