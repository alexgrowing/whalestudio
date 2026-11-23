import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDefStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PowPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.SiegelPower

def siegLam (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] (P : PolAV (Sp R)) [IsCommMonObj P.A] :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := P.A
  ab := P.isAb
  P := abelian₂ P.A P.L
  isLB := LB.isLB_linComb P.isLB _ _
  rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG P.isAb (pull_isLB (LB.isLB_linComb P.isLB _ _) _) _

theorem det_eq_one {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hpd : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (hdet : IsUnit (W + W.transpose).det) : (W + W.transpose).det = 1 := by
  have h₁ := hpd.det_pos
  have h₂ : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).det = (((W + W.transpose).det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det _).symm
  rw [h₂] at h₁
  rcases Int.isUnit_iff.1 hdet with h | h
  · exact h
  · rw [h] at h₁; norm_num at h₁

theorem exists_pow_polAV : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (P' : PolAV (Sp R)) (pr : Fin r → (P'.A ⟶ P.A)), (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk P'.A pr)) ∧ P'.g = r * P.g ∧ LBIso P'.L (LB.LinComb P.L (tensφ pr) (tensε W)) := by
  intro R _ _ _ _ P r W hpd hdet
  have := P.isAb.comm
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := siegLam hG P
  have hP : c.P.IsLB := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hfin : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := inferInstanceAs (IsFinite (𝟙 P.A.left))
  have hamp : RelAmple c.A c.diag := by
    have e := lbIso_diag L₁ P
    have h := relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB hfin
    exact (relAmple_finite_pow_iso (Sp R) P.A P.A (𝟙 _) (lbPow P.L 2) 1 one_pos P.isAb P.isAb
      (LB.isLB_linComb P.isLB _ _) hfin).2.2.2 _ hD e (h.2.1.2 P.ample)
  let G := Out.powObj P.A r
  let pr : Fin r → (G ⟶ P.A) := Out.powPr P.A
  have hpr : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have hu : ∀ (T : Over (Sp R)) (y : Fin r → (T ⟶ P.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit P.A r).lift (Fan.mk T y), fun u => (Out.powIsLimit P.A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit P.A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hB : ∀ (T : Over (Sp R)) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG (Sp R) c.A c.diag c.ab hD hamp c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  refine ⟨{ A := G
            isAb := isAbelianScheme_powObj_of_isAbelianScheme P.A P.isAb r
            g := r * P.g
            smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ r P.smoothDim
            L := sharp c.P pr W
            isLB := hLB
            rigid := rigidified_sharp hP pr W hpr hB
            sym := sym_sharp hP pr W hpr hB hs
            ample := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG 0 1 r R 1 (Sp R) (𝟙 _) c G pr W hpr hu hamp hpd
            ktriv := kTriv_sharp hP pr W hpr hB hs hu (det_eq_one W hpd hdet)
              (fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx) }, pr, hpr, ⟨Out.powIsLimit P.A r⟩, rfl, ?_⟩
  refine lbIso_nested P.isLB _ _ (fun uv : Fin r × Fin r => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ _ ?_
  simp only [prod_lam (pr _) (pr _) (PrimNorm.cls P.L)]
  rw [Fintype.prod_prod_type (f := fun k : (Fin r × Fin r) × Fin 4 => PrimNorm.cls P.L (tensφ pr k) ^ tensε W k)]
  refine Finset.prod_congr rfl fun uv _ => ?_
  simp only [Fin.prod_univ_four, tensφ, tensε, GlobalTheory.PolDeg.lamPts, Oε, diff₂, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, zpow_mul]
  simp only [zpow_one, zpow_neg, mul_zpow, inv_zpow]

end GlobalTheory.Mum.PowPol
