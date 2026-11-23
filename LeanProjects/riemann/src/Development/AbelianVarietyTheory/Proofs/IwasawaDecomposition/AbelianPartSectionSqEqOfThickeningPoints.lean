import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqDescend

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_sq_le (φ : K → (Y ⟶ X)) (p : K → Fin 1 → L.ι) :
    LB.wchart (SqLB.sq L) φ p ≤ LB.wchart L φ (fun k => p k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0

theorem gm_sq_g' (f : Y ⟶ X) (y : Y) (j j' : Fin 1 → L.ι) (hj : f y ∈ (SqLB.sq L).U j)
    (hj' : f y ∈ (SqLB.sq L).U j') :
    gm f y ((SqLB.sq L).U j ⊓ (SqLB.sq L).U j') ((SqLB.sq L).g j j') =
      gm f y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ (2 : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = fun _ => b := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  exact SqLB.gm_sq_g f y (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0)

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem trF_sq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) (p p' : K → Fin 1 → L.ι)
    (hy : y ∈ LB.wchart (SqLB.sq L) φ p ⊓ LB.wchart (SqLB.sq L) φ p') :
    (∏ k, gm (𝟙 Y ≫ φ k) y ((SqLB.sq L).U (p k) ⊓ (SqLB.sq L).U (p' k)) ((SqLB.sq L).g (p k) (p' k)) ^ ε k) =
      trF φ ε (𝟙 Y) y (fun k => p k 0) (fun k => p' k 0) ^ 2 := by
  simp only [trF]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g' (𝟙 Y ≫ φ k) y (p k) (p' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k), ← zpow_mul, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

def sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb (SqLB.sq L) φ ε) where
  f := fun p => (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0)) *
    (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))
  compat := fun p p' => fn_ext fun y hy => by
    have h₁ := wchart_sq_le φ p hy.1
    have h₂ := wchart_sq_le φ p' hy.2
    have eA : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p k 0)) (s.f (fun k => p k 0)) := gs_res (𝟙 Y) y _ hy.1 _
    have eB : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p')).op).hom (s.f (fun k => p' k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p' k 0)) (s.f (fun k => p' k 0)) := gs_res (𝟙 Y) y _ hy.2 _
    have eL := (gs_res (𝟙 Y) y inf_le_left hy _).trans ((gs_mul (𝟙 Y) y _ hy.1 _ _).trans (congrArg₂ (· * ·) eA eA))
    have eR := (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb (SqLB.sq L) φ ε (𝟙 Y) y p p' hy.1 hy.2).trans (trF_sq φ ε y p p' hy))))
      ((gs_res (𝟙 Y) y inf_le_right hy _).trans ((gs_mul (𝟙 Y) y _ hy.2 _ _).trans (congrArg₂ (· * ·) eB eB))))
    refine eL.trans (Eq.trans ?_ eR.symm)
    rw [sec_trans s (𝟙 Y) y h₁ h₂, Units.val_pow_eq_pow_val]
    ring

theorem good_sq {J : (Z ⟶ X) → L.ι} {z : Z} (hJ : Good L z J) : Good (SqLB.sq L) z (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => hJ ψ

theorem sval_sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (sqSec s) r z (fun q _ => J q) = sval s r z J ^ 2 := by
  have h0 := hJ.mem φ r
  have hm : r z ∈ LB.wchart (SqLB.sq L) φ (fun k _ => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h0 k
  exact (gs_mul r z _ hm _ _).trans ((congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _)).trans
    (pow_two _).symm)

def secSub {M : LB Y} (a b : LB.Sec M) : LB.Sec M where
  f := fun i => a.f i - b.f i
  compat := fun i j => by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

theorem sval_secSub {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    sval (secSub a b) r z J = sval a r z J - sval b r z J :=
  gs_sub r z _ (hJ.mem φ r) _ _

end GlobalTheory.SqDescend

open GlobalTheory.SqDescend in

theorem GlobalTheory.sq_corr_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w hw hpG α α' hφ s s' hE Z ρ z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM : (SqLB.sq D.toPre.P.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hM' : (SqLB.sq D'.toPre.P.L).IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ Φ.hom.left hM hM' w hw (Fin 4)
    (D'.toPre.famφB α') (D.toPre.famφB α) (DegPre.famε 2) Φ.hom.left hφ (sqSec s)
  have hT : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      sval s (r ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval a r z (fun q _ => J' q) := by
    intro Z r z J J' hJ hJ'
    rw [← sval_sqSec s _ z hJ]
    exact ExpTrans.sec_val w _ _ _ Φ.hom.left hφ (sqSec s) a r z (ha Z r z) (good_sq hJ) (good_sq hJ')
  have hvan : ∀ (e : ℕ) (q : Fin 4 → Fin 1 → D'.toPre.P.L.ι),
      ((U'.gt e).pG.left.app _).hom ((secSub a (sqSec s')).f q) = 0 := by
    intro e q
    refine fn_ext fun y hy => ?_
    choose J₁ hJ₁ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left =>
      exists_chart hL (ψ y)
    choose J₂ hJ₂ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left =>
      exists_chart hL' (ψ y)
    have g₁ : Good D.toPre.P.L y J₁ := hJ₁
    have g₂ : Good D'.toPre.P.L y J₂ := hJ₂
    have e1 := hE e _ (𝟙 _) y J₁ J₂ g₁ g₂
    have e2 := hT _ (U'.gt e).pG.left y J₁ J₂ g₁ g₂
    simp only [Category.id_comp] at e1
    rw [hpG e, e1, ← sval_sqSec s' _ y g₂] at e2
    have e3 := (Units.mul_right_inj _).1 e2
    have hΔ : sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0 := by
      rw [sval_secSub a (sqSec s') _ y (good_sq g₂), e3, sub_self]
    refine (gs_pull (𝟙 _) (U'.gt e).pG.left y _ hy _).trans ?_
    rw [Category.id_comp, gs_zero]
    refine (sec_trans (secSub a (sqSec s')) (U'.gt e).pG.left y (j := q) hy ((good_sq g₂).mem _ _)).trans ?_
    change _ * sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0
    rw [hΔ, mul_zero]
  obtain ⟨hN, -, -, -⟩ := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have := D'.toPre.P.isAb.smooth
  have := D'.toPre.P.isAb.geomConnected
  have h0 := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) hI D'.toPre.P.A).1 _
    (DVR.linComb_isLB _ hM' _ _) (secSub a (sqSec s'))
    fun e q => (ExtDiv.pG_app_eq_zero_iff (U'.gt e) _ _).1 (hvan e q)
  have key : sval a ρ z (fun q _ => J' q) = sval (sqSec s') ρ z (fun q _ => J' q) := by
    have h1 : sval (secSub a (sqSec s')) ρ z (fun q _ => J' q) = 0 := by
      show gs _ _ _ _ = 0
      exact (congrArg (gs ρ z _) (h0 _)).trans (gs_zero _ _ _)
    have h2 := sval_secSub a (sqSec s') ρ z (good_sq hJ')
    rw [h1] at h2
    exact sub_eq_zero.1 h2.symm
  rw [hT Z ρ z J J' hJ hJ', key, sval_sqSec s' ρ z hJ']
