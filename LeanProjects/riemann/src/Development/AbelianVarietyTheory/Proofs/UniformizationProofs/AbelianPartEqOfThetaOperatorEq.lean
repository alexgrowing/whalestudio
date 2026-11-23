import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOfIsGenTransl
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiBase

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (t : Y' ⟶ Y) (g : Y' ⟶ X)
    (hg : t ≫ f = g) (θ : LB.Sec (L.pull f)) : ∃ θ' : LB.Sec (L.pull g),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
        sval (L := L) (φ := fun _ : PUnit => g) (ε := fun _ => 1) θ' r z J =
          sval (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ (r ≫ t) z J := by
  subst hg
  obtain ⟨θ', h⟩ := exists_sec hL (φ' := fun _ : PUnit => t ≫ f) (ε' := fun _ => 1)
    (fun U _ h => by simp [Fintype.prod_sum_type])
    (pullMulSec (L := L) (φ := fun _ : PUnit => f) (ε := fun _ => 1) θ t (LB.oneGen L (Y := Y'))
      (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
  refine ⟨θ', fun Z r z J hJ => ?_⟩
  refine (h Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

theorem trPt_inv_comp {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (b : TF (R := R) F ⟶ D.P.A) :
    DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, DVR.tr_fst, DVR.tr_fst, Category.id_comp]
  · have : (DegPre.trPt D F b⁻¹ ≫ DegPre.trPt D F b) ≫ DegPre.prB D F = DegPre.prB D F := by
      rw [Category.assoc, DVR.tr_pr, MonObj.comp_mul, DVR.tr_pr, ← Category.assoc, DVR.tr_fst, _root_.mul_assoc,
        ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one]
    exact this.trans (Category.id_comp _).symm

theorem prod_comp_fam_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (t : DegPre.BF D F ⟶ DegPre.BF D F) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (t.left ≫ DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (t ≫ DegPre.prB D F).left ^ k :=
  ThetaPow.prod_fam_zero D F k (fun q => h (t.left ≫ q))

theorem b_eq_of_phiRel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b := by
  intro hG hT R _ _ D hB F _ _ n hn p p' w w' hw hw' H hy
  have hL := D.P.isLB
  obtain ⟨θ, σ, hθ, hσ⟩ := ThetaPow.exists_theta_pow hT R D F n hn
  obtain ⟨s, hs, -⟩ := FamFree.exists_fam_single hG hB hn 0 σ
  obtain ⟨s', h₁, h₂⟩ := H s
  have v₁ := (DVR.phiRel_iff hG p w hw s s').1 h₁ 0 p.y (zero_add _) _ (𝟙 _)
  have v₂ := (DVR.phiRel_iff hG p' w' hw' s s').1 h₂ 0 p.y ((zero_add _).trans hy) _ (𝟙 _)
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := DVR.gen_phi hG p w hw 0
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := DVR.gen_phi hG p' w' hw' 0
  obtain ⟨θ₁, hθ₁⟩ := exists_pull_sec hL (DegPre.prB D F).left (DegPre.trPt D F p.g.b).left
    (DegPre.trPt D F p.g.b ≫ DegPre.prB D F).left rfl θ
  obtain ⟨θ₂, hθ₂⟩ := exists_pull_sec hL (DegPre.prB D F).left (DegPre.trPt D F p'.g.b).left
    (DegPre.trPt D F p'.g.b ≫ DegPre.prB D F).left rfl θ
  obtain ⟨v, hvg, hvv⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(DegPre.trPt D F p.g.b ≫ DegPre.prB D F).left, (DegPre.trPt D F p'.g.b ≫ DegPre.prB D F).left])
    (ε' := ![(n : ℤ), -(n : ℤ)]) (fun U _ h => by
      have a := prod_comp_fam_zero D F n (DegPre.trPt D F p.g.b) h
      have a' := prod_comp_fam_zero D F n (DegPre.trPt D F p'.g.b) h
      have c : ∏ i, h (DegPre.famφ D F (0 + p'.y) i) ^ DegPre.famε n i =
        ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε n i := by rw [hy]
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (DVR.prod_neg _ _ a'))
        (DVR.prod_neg _ _ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
          (c := ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε n i) rfl (DVR.prod_neg _ _ a)))) ?_
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast]
      rw [mul_inv, inv_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul, _root_.mul_comm])
    (LB.mulGen D.P.L _ _ _ _ u' (LB.invGen D.P.L _ _ u))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu' (DVR.invGen_isGen _ _ _ _ hu))
  obtain ⟨hI, hN⟩ := degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk R D F
  have hne : ∃ j, θ₂.f j ≠ 0 := by
    by_contra h0
    have h0' : ∀ j, θ₂.f j = 0 := fun j => by_contra fun hj => h0 ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hθ
    refine hj (sec_ext_val (L := D.P.L) (φ := fun _ : PUnit => (DegPre.prB D F).left) (ε := fun _ => 1) (s := θ)
      (s' := DVR.SecOps.secZero) hL (fun y J hJ => ?_) j)
    have e := hθ₂ _ (DegPre.trPt D F p'.g.b⁻¹).left y J hJ
    rw [← Over.comp_left, trPt_inv_comp, Over.id_left] at e
    rw [← e, DVR.UUA.sval_zero_of h0' _ y J (hJ.mem _ _),
      DVR.UUA.sval_zero_of (s := DVR.SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow _ _ hN D.P.L hL _ _ n hn θ₁ θ₂ v hvg hne (fun y J hJ => by
    have e₁ := v₁ y J hJ
    have e₂ := v₂ y J hJ
    rw [← hv u hu hc _ (𝟙 _) y J hJ, hs, hσ _ _ y J hJ] at e₁
    rw [← hv' u' hu' hc' _ (𝟙 _) y J hJ, hs, hσ _ _ y J hJ] at e₂
    have e := e₁.symm.trans e₂
    have f₁ := hθ₁ _ (𝟙 _) y J hJ
    have f₂ := hθ₂ _ (𝟙 _) y J hJ
    simp only [Category.id_comp, Over.id_left] at e f₁ f₂
    rw [← f₁, ← f₂] at e
    rw [hvv _ _ y J hJ, val_mul hJ, val_inv, Units.val_mul, mul_right_comm, _root_.mul_comm (Units.val _)]
    exact ((Units.eq_mul_inv_iff_mul_eq _).2 e))
  exact eq_of_isGen_transl R D F _ _ r hr

end GlobalTheory.PhiBase
