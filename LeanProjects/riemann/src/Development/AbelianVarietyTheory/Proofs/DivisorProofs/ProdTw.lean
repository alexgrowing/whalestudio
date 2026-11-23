import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A)
  (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)

theorem prod_tw {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (x.left ≫ twφ D₀ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have hu : x ≫ toUnit D₀.P.A = toUnit T := toUnit_unique _ _
  rw [Fin.prod_univ_three]
  show h (x ≫ (β * (toUnit D₀.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₀.P.A ≫ b).left ^ (-1 : ℤ) *
    h (x ≫ toUnit D₀.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
  rfl

theorem lift_β {T : Over (Sp R)} (p q : T ⟶ D₀.P.A) :
    (lift p q).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left =
      (lift (p ≫ β) (q ≫ β)).left := by
  rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

variable {D₀ D β b} [IsMonHom β]

theorem wv_mul {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    {T : Over (Sp R)} (x y : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w (x * y).left z J J' * wv w (1 : T ⟶ D₀.P.A).left z J J' *
        lamVal wΛ (lift (1 : T ⟶ D₀.P.A) (1 : T ⟶ D₀.P.A)).left z J J' =
      wv w x.left z J J' * wv w y.left z J J' * lamVal wΛ (lift x y).left z J J' *
        cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⊗ B₀ ⟶ B₀ := fst B₀ B₀
  let s : B₀ ⊗ B₀ ⟶ B₀ := snd B₀ B₀
  have H := (((((reg_wv hw (f * s).left).mul (reg_wv hw f.left).inv).mul (reg_wv hw s.left).inv).mul
    (reg_wv hw (1 : B₀ ⊗ B₀ ⟶ B₀).left)).mul (reg_lam hΛ (lift f s).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left).inv
  have ev : ∀ x y : T ⟶ B₀,
      wv w ((lift x y).left ≫ (f * s).left) z J J' * (wv w ((lift x y).left ≫ f.left) z J J')⁻¹ *
        (wv w ((lift x y).left ≫ s.left) z J J')⁻¹ * wv w ((lift x y).left ≫ (1 : B₀ ⊗ B₀ ⟶ B₀).left) z J J' *
        (lamVal wΛ ((lift x y).left ≫ (lift f s).left) z J J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          ((lift x y).left ≫ (lift (f ≫ β) (lift (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b))).left) z J)⁻¹ =
      wv w (x * y).left z J J' * (wv w x.left z J J')⁻¹ * (wv w y.left z J J')⁻¹ *
        wv w (1 : T ⟶ B₀).left z J J' * (lamVal wΛ (lift x y).left z J J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (y ≫ β) (toUnit T ≫ b))⁻¹ := fun x y => by
    have hu : lift x y ≫ toUnit (B₀ ⊗ B₀) = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [MonObj.comp_mul, MonObj.comp_one, comp_lift, comp_lift, comp_lift, ← Category.assoc (lift x y) (toUnit _), hu,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, prod_tw, prod_tw, lift_β, prod_lam, prod_lam]
      erw [prod_cub (G := D.P.A) (f ≫ β) (s ≫ β) (toUnit (B₀ ⊗ B₀) ≫ b) h]
      rw [MonObj.mul_comp, MonObj.one_comp,
        _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    ((snd B₀ B₀).left ≫ B₀.hom) (surj_comp (surj_snd hG D₀.P.isAb _) (hG _ _ D₀.P.isAb).2)
    (lift x y).left (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left (by
      rw [Over.w, Over.w, Over.w]) z hJ hJ'
  have E' := (ev x y).symm.trans (E.trans (ev 1 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, _root_.mul_one (1 : T ⟶ B₀)] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

theorem wv_inv (hb : padd D.P.A b b = η[D.P.A]) {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen)
    {T : Over (Sp R)} (x : T ⟶ D₀.P.A) {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') :
    wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) =
      wv w (x⁻¹).left z J J' * val D₀.sym x.left z J' * cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b) := by
  have hG := GlobalTheory.globalFns_holds
  let B₀ := D₀.P.A
  let f : B₀ ⟶ B₀ := 𝟙 B₀
  have hbb : (toUnit B₀ ≫ b) * (toUnit B₀ ≫ b) = 1 := by
    rw [← MonObj.comp_mul]; exact congrArg (toUnit B₀ ≫ ·) hb
  have H := (((((reg_wv hw f.left).mul (reg_val (L' := D₀.P.L) D.sym_gen (f ≫ β).left)).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left)).mul (reg_wv hw (f⁻¹).left).inv).mul
      (reg_val' (L := D.P.L) D₀.sym_gen f.left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left).inv
  have ev : ∀ x : T ⟶ B₀,
      wv w (x.left ≫ f.left) z J J' * val D.sym (x.left ≫ (f ≫ β).left) z J *
        val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (toUnit B₀ ≫ b) (toUnit B₀ ≫ b))).left) z J *
        (wv w (x.left ≫ (f⁻¹).left) z J J')⁻¹ * (val D₀.sym (x.left ≫ f.left) z J')⁻¹ *
        (val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
          (x.left ≫ (lift (f ≫ β) (lift (f ≫ β)⁻¹ (toUnit B₀ ≫ b))).left) z J)⁻¹ =
      wv w x.left z J J' * val D.sym (x ≫ β).left z J * cubV D.cub z J (x ≫ β) (toUnit T ≫ b) (toUnit T ≫ b) *
        (wv w (x⁻¹).left z J J')⁻¹ * (val D₀.sym x.left z J')⁻¹ *
        (cubV D.cub z J (x ≫ β) (x ≫ β)⁻¹ (toUnit T ≫ b))⁻¹ := fun x => by
    have hu : x ≫ toUnit B₀ = toUnit T := toUnit_unique _ _
    simp only [← Over.comp_left]
    rw [comp_lift, comp_lift, comp_lift, comp_lift, ← Category.assoc x (toUnit _), hu, GrpObj.comp_inv, GrpObj.comp_inv,
      ← Category.assoc x f, Category.comp_id]
    rfl
  have E := H.rigid D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ * _ * _ = _
      rw [prod_tw, prod_tw, GlobalTheory.GaugeValues.prod_sym, GlobalTheory.GaugeValues.prod_sym]
      erw [prod_cub (G := D.P.A) (f ≫ β) (toUnit B₀ ≫ b) (toUnit B₀ ≫ b) h,
        prod_cub (G := D.P.A) (f ≫ β) (f ≫ β)⁻¹ (toUnit B₀ ≫ b) h]
      rw [GrpObj.inv_comp,
        _root_.mul_assoc (f ≫ β), hbb, _root_.mul_one (f ≫ β), mul_inv_cancel (f ≫ β), _root_.one_mul (toUnit B₀ ≫ b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
    B₀.hom (hG _ _ D₀.P.isAb).2 x.left (1 : T ⟶ B₀).left (by rw [Over.w, Over.w]) z hJ hJ'
  have E' := (ev x).symm.trans (E.trans (ev 1))
  rw [MonObj.one_comp, (isCub_cubV D.cub hJ).face, (isCub_cubV D.cub hJ).face, inv_one,
    GlobalTheory.GaugeValues.val_sym_one D hJ, GlobalTheory.GaugeValues.val_sym_one D₀ hJ'] at E'
  apply Additive.ofMul.injective
  have e := congrArg Additive.ofMul E'
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e ⊢
  linear_combination (norm := abel) e

end GlobalTheory.MumCmp.Point
