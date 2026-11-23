import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdTw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_unit_of_sq [IsIntegrallyClosed R] (a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ)
    (a' : Γ(Spec (CommRingCat.of R), ⊤)ˣ) (h : a * a = pullU (jK R) ⊤ a') :
    ∃ u : Γ(Spec (CommRingCat.of R), ⊤)ˣ, pullU (jK R) ⊤ u = a := by
  let φ := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  let φK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
  have nat : ∀ r : R, (jK R).appTop.hom (φ r) = φK (algebraMap R (FractionRing R) r) := fun r =>
    (congrArg (fun q => q.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))).symm
  obtain ⟨k, hk⟩ := φK.surjective a.val
  obtain ⟨r, hr⟩ := φ.surjective a'.val
  have e : (show FractionRing R from k) ^ 2 = algebraMap R (FractionRing R) r := by
    apply φK.injective
    rw [← nat, hr, sq]
    exact (map_mul φK k k).trans (by rw [hk]; exact congrArg Units.val h)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := FractionRing R)
    (x := k) two_pos (by rw [e]; exact isIntegral_algebraMap)
  have e' : s * s = r := IsFractionRing.injective R (FractionRing R) (by rw [map_mul, hs, ← e, sq])
  have hu : IsUnit (φ s) := isUnit_of_mul_isUnit_left (y := φ s) (by
    rw [← map_mul φ s s]
    exact (congrArg IsUnit ((congrArg φ e').trans hr)).mpr a'.isUnit)
  refine ⟨hu.unit, Units.ext ?_⟩
  show (jK R).appTop.hom (φ s) = _
  rw [nat, hs, hk]

theorem prod_gt (D : DegPre R) {T T' : Over (Sp R)} (ρ : T' ⟶ T) (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h ((toUnit T' ≫ D.c χ) * (ρ ≫ b)).left)⁻¹ * h (toUnit T' ≫ D.c χ).left * h (ρ ≫ b).left *
        (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  have hu : ρ ≫ toUnit T = toUnit T' := toUnit_unique _ _
  rw [Fin.prod_univ_four]
  show h (ρ ≫ ((toUnit T ≫ D.c χ) * b)).left ^ (-1 : ℤ) * h (ρ ≫ toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h (ρ ≫ b).left ^ (1 : ℤ) * h (ρ ≫ toUnit T ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
  rw [MonObj.comp_mul, ← Category.assoc ρ, ← Category.assoc ρ, hu, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
  rfl

variable {D₀ D : DegPre R} {β : D₀.P.A ⟶ D.P.A} {b : 𝟙_ (Over (Sp R)) ⟶ D.P.A} [IsMonHom β]

theorem exists_normalised {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hw : w.IsGen) :
    ∃ w' : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε), w'.IsGen ∧
      ∀ (T : Over (Sp R)) (z : T.left) J J', Good D.P.L z J → Good D₀.P.L z J' →
        wv w' (1 : T ⟶ D₀.P.A).left z J J' * val D₀.rig (toUnit T).left z J' = val D.rig (toUnit T).left z J := by
  let E := 𝟙_ (Over (Sp R))
  obtain ⟨a, ha⟩ := (((reg_val (L' := D₀.P.L) D.rig_gen (toUnit E).left).mul
    (reg_wv hw (1 : E ⟶ D₀.P.A).left).inv).mul (reg_val' (L := D.P.L) D₀.rig_gen (toUnit E).left).inv).glue
    D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ = _
      rw [prod_tw, Fintype.prod_unique, Fintype.prod_unique, MonObj.one_comp, _root_.one_mul]
      show h (1 : E ⟶ D.P.A).left ^ (1 : ℤ) * _ * (h' (1 : E ⟶ D₀.P.A).left ^ (1 : ℤ))⁻¹ = 1
      apply Additive.ofMul.injective
      simp only [zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨scale (pullU (toUnit D₀.P.A).left ⊤ a) w, scale_isGen _ hw, fun T z J J' hJ hJ' => ?_⟩
  have e := ha _ (toUnit T).left z J J' hJ hJ'
  have e₁ : (toUnit T).left ≫ (toUnit E).left = (toUnit T).left := congrArg (·.left) (toUnit_unique (toUnit T ≫ toUnit E) _)
  have e₂ : (toUnit T).left ≫ (1 : E ⟶ D₀.P.A).left = (1 : T ⟶ D₀.P.A).left :=
    congrArg (fun q : T ⟶ D₀.P.A => q.left) (MonObj.comp_one (toUnit T))
  have e₃ : (1 : T ⟶ D₀.P.A).left ≫ (toUnit D₀.P.A).left = (toUnit T).left :=
    congrArg (·.left) (toUnit_unique ((1 : T ⟶ D₀.P.A) ≫ toUnit D₀.P.A) _)
  simp only [e₁, e₂] at e
  have s : wv (scale (pullU (toUnit D₀.P.A).left ⊤ a) w) (1 : T ⟶ D₀.P.A).left z J J' =
      gm (toUnit T).left z ⊤ a * wv w (1 : T ⟶ D₀.P.A).left z J J' :=
    (gm_scale (pullU (toUnit D₀.P.A).left ⊤ a) w (1 : T ⟶ D₀.P.A).left z
      (fun k => J ((1 : T ⟶ D₀.P.A).left ≫ twφ D₀ D β b k), J' (1 : T ⟶ D₀.P.A).left) ⟨hJ.mem _ _, hJ' _⟩).trans (congrArg (· * _)
      ((gm_pull _ (toUnit D₀.P.A).left z ⊤ trivial a).trans (by rw [e₃])))
  rw [s, ← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def sv (xe : D₀.X ≃+ D.X) (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)) (χ : D₀.X) (z : (TK R).left)
    (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι) :
    ((TK R).left.presheaf.stalk z)ˣ :=
  (wv w (toUnit (TK R) ≫ D₀.c χ).left z J J')⁻¹ * val (D₀.psi χ) (𝟙 _) z J' * (val (D.psi (xe χ)) (𝟙 _) z J)⁻¹

theorem cK_add (D : DegPre R) (T : Over (Sp R)) (χ χ' : D.X) :
    toUnit T ≫ D.c (χ + χ') = (toUnit T ≫ D.c χ) * (toUnit T ≫ D.c χ') := by
  rw [D.c_add, ← MonObj.comp_mul]; rfl

theorem cK_zero (D : DegPre R) (T : Over (Sp R)) : toUnit T ≫ D.c 0 = 1 := PsiZero.cPoint_zero' D T

theorem cK_neg (D : DegPre R) (T : Over (Sp R)) (χ : D.X) : toUnit T ≫ D.c (-χ) = (toUnit T ≫ D.c χ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← cK_add, neg_add_cancel, cK_zero])

theorem val_rigK (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK R)).left z J :=
  (val_pull hJ _ _ _).trans (by rw [Category.id_comp])

theorem val_tau' (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a a' : D.X) :
    val (D.tau a a') (𝟙 _) z J = val (D.psi (a + a')) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi a') (𝟙 _) z J)⁻¹ * (val D.rig (toUnit (TK R)).left z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans (congrArg (·⁻¹) (val_rigK D hJ))))

theorem val_psi_neg {D : DegPre R} (hE : D.PsiEven) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (χ : D.X) :
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (toUnit (TK R) ≫ D.c χ).left z J = val (D.psi χ) (𝟙 _) z J := by
  refine Eq.trans ?_ (val_corr hJ (hE χ) (𝟙 _))
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm
  rw [Category.id_comp]

section Laws

variable {xe : D₀.X ≃+ D.X} {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)}
  {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι} {J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι}

omit [IsMonHom β] in
theorem sv_zero (hB₀ : D₀.TauBimult) (hB : D.TauBimult) (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J')
    (hn : wv w (1 : TK R ⟶ D₀.P.A).left z J J' * val D₀.rig (toUnit (TK R)).left z J' =
      val D.rig (toUnit (TK R)).left z J) : sv xe w 0 z J J' = 1 := by
  have p₀ : val (D₀.psi 0) (𝟙 _) z J' = (val D₀.rig (toUnit (TK R)).left z J')⁻¹ := PsiZero.val_psi_zero hB₀ hJ'
  have p : val (D.psi 0) (𝟙 _) z J = (val D.rig (toUnit (TK R)).left z J)⁻¹ := PsiZero.val_psi_zero hB hJ
  have q : val (D.psi (xe 0)) (𝟙 _) z J = val (D.psi 0) (𝟙 _) z J := by rw [map_zero]
  rw [sv, q, p₀, p, cK_zero, ← hn]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem sv_add (hB₀ : D₀.TauBimult) (hB : D.TauBimult) (hc : ∀ χ, D₀.c χ ≫ β = D.c (xe χ)) (hw : w.IsGen)
    {wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D.P.A D.P.L).pull
      (lift (fst D₀.P.A D₀.P.A ≫ β) (snd D₀.P.A D₀.P.A ≫ β) : G2 D₀.P.A ⟶ G2 D.P.A).left)} (hΛ : wΛ.IsGen)
    (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J')
    (hτ : ∀ a a' : D₀.X, val (D₀.tau a a') (𝟙 _) z J' =
      lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
        val (D.tau (xe a) (xe a')) (𝟙 _) z J)
    (hn : wv w (1 : TK R ⟶ D₀.P.A).left z J J' * val D₀.rig (toUnit (TK R)).left z J' =
      val D.rig (toUnit (TK R)).left z J) (χ χ' : D₀.X) :
    sv xe w (χ + χ') z J J' *
        cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ D.c (xe χ')) (toUnit (TK R) ≫ b) =
      sv xe w χ z J J' * sv xe w χ' z J J' := by
  have p₀ : val (D₀.psi 0) (𝟙 _) z J' = (val D₀.rig (toUnit (TK R)).left z J')⁻¹ := PsiZero.val_psi_zero hB₀ hJ'
  have p : val (D.psi 0) (𝟙 _) z J = (val D.rig (toUnit (TK R)).left z J)⁻¹ := PsiZero.val_psi_zero hB hJ
  have q₀ : ∀ a a' : D₀.X, a = a' → val (D₀.psi a) (𝟙 _) z J' = val (D₀.psi a') (𝟙 _) z J' := by rintro a a' rfl; rfl
  have q : ∀ a a' : D.X, a = a' → val (D.psi a) (𝟙 _) z J = val (D.psi a') (𝟙 _) z J := by rintro a a' rfl; rfl
  have t₀ := hτ 0 0
  rw [val_tau' D₀ hJ', val_tau' D hJ, q₀ (0 + 0) 0 (add_zero 0), q (xe 0 + xe 0) 0 (by simp), q (xe 0) 0 (map_zero xe),
    p₀, p, cK_zero] at t₀
  have t := hτ χ χ'
  rw [val_tau' D₀ hJ', val_tau' D hJ, q (xe χ + xe χ') (xe (χ + χ')) (map_add xe χ χ').symm] at t
  have m := wv_mul hw hΛ (toUnit (TK R) ≫ D₀.c χ) (toUnit (TK R) ≫ D₀.c χ') hJ hJ'
  rw [Category.assoc, Category.assoc, hc, hc, ← cK_add] at m
  unfold sv
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₀; have a₂ := E t; have a₃ := E m; have a₄ := E hn
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₂ - a₁ - a₃ + a₄

theorem sv_sq (hE₀ : D₀.PsiEven) (hE : D.PsiEven) (hc : ∀ χ, D₀.c χ ≫ β = D.c (xe χ)) (hw : w.IsGen)
    (hb : padd D.P.A b b = η[D.P.A]) (hJ : Good D.P.L z J) (hJ' : Good D₀.P.L z J') (h0 : sv xe w 0 z J J' = 1)
    (χ : D₀.X) (hadd : sv xe w (χ + -χ) z J J' *
        cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ D.c (xe (-χ))) (toUnit (TK R) ≫ b) =
      sv xe w χ z J J' * sv xe w (-χ) z J J') :
    sv xe w χ z J J' * sv xe w χ z J J' =
      cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ b) (toUnit (TK R) ≫ b) := by
  have q : ∀ a a' : D.X, a = a' → val (D.psi a) (𝟙 _) z J = val (D.psi a') (𝟙 _) z J := by rintro a a' rfl; rfl
  rw [add_neg_cancel, h0, map_neg, cK_neg] at hadd
  have e₀ := val_psi_neg hE₀ hJ' χ
  have e := val_psi_neg hE hJ (xe χ)
  have m := wv_inv hb hw (toUnit (TK R) ≫ D₀.c χ) hJ hJ'
  rw [Category.assoc, hc] at m
  unfold sv at hadd ⊢
  rw [cK_neg, q (xe (-χ)) (-xe χ) (map_neg xe χ)] at hadd
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₀; have a₂ := E e; have a₃ := E m; have a₄ := E hadd
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₂ - a₁ - a₃ - a₄

end Laws

theorem exists_coord [IsLocalRing R] [IsIntegrallyClosed R] {xe : D₀.X ≃+ D.X}
    {w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β b) twε)} (hc : ∀ χ, D₀.c χ ≫ β = D.c (xe χ)) (hw : w.IsGen)
    (hb : padd D.P.A b b = η[D.P.A]) (χ : D₀.X)
    (hs : ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' → sv xe w χ z J J' * sv xe w χ z J J' =
      cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ b) (toUnit (TK R) ≫ b)) :
    ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D (𝟙_ (Over (Sp R))) b (xe χ)) DegPre.gtε), s.IsGen ∧
      ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' →
        val s (toUnit (TK R)).left z J = sv xe w χ z J J' := by
  let E := 𝟙_ (Over (Sp R))
  have hbb : b * b = 1 := hb.trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp])
  obtain ⟨σ, hσ⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (DegPre.gtφT D E b (xe χ)) DegPre.gtε
  obtain ⟨a, ha⟩ := ((((reg_wv hw (toUnit (TK R) ≫ D₀.c χ).left).inv.mul
    (reg_val' (L := D.P.L) (D₀.psi_gen χ) (𝟙 _))).mul (reg_val (L' := D₀.P.L) (D.psi_gen (xe χ)) (𝟙 _)).inv).mul
    (reg_val (L' := D₀.P.L) (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) hσ (toUnit (TK R)).left).inv).glue
    D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ * _ = _
      rw [prod_tw, prod_gt, Fintype.prod_unique, Fintype.prod_unique, Category.id_comp, Category.id_comp,
        Category.assoc, hc]
      apply Additive.ofMul.injective
      simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  obtain ⟨a', ha'⟩ := (((reg_val (L' := D₀.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
      (lift (toUnit E ≫ D.c (xe χ)) (lift b b)).left).mul
    (reg_val (L' := D₀.P.L) (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) hσ (𝟙 E : E ⟶ E).left).inv).mul
    (reg_val (L' := D₀.P.L) (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) hσ (𝟙 E : E ⟶ E).left).inv).glue
    D.P.isLB D₀.P.isLB (fun U _ h h' => by
      show _ * _ * _ = _
      rw [prod_gt]
      erw [prod_cub (G := D.P.A) (toUnit E ≫ D.c (xe χ)) b b h]
      rw [Category.id_comp, _root_.mul_assoc (toUnit E ≫ D.c (xe χ)), hbb, _root_.mul_one (toUnit E ≫ D.c (xe χ))]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  have va : ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' →
      sv xe w χ z J J' * (val (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) σ (toUnit (TK R)).left z J)⁻¹ =
        gm (𝟙 (TK R).left) z ⊤ a := fun z J J' hJ hJ' => by
    have e := ha _ (𝟙 _) z J J' hJ hJ'
    simp only [Category.id_comp] at e
    exact e
  have va' : ∀ (z : (TK R).left) J J', Good D.P.L z J → Good D₀.P.L z J' →
      cubV D.cub z J (toUnit (TK R) ≫ D.c (xe χ)) (toUnit (TK R) ≫ b) (toUnit (TK R) ≫ b) *
        (val (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) σ (toUnit (TK R)).left z J)⁻¹ *
        (val (φ := DegPre.gtφT D E b (xe χ)) (ε := DegPre.gtε) σ (toUnit (TK R)).left z J)⁻¹ =
        gm (toUnit (TK R)).left z ⊤ a' := fun z J J' hJ hJ' => by
    have e := ha' _ (toUnit (TK R)).left z J J' hJ hJ'
    have hu : toUnit (TK R) ≫ toUnit E = toUnit (TK R) := toUnit_unique _ _
    simp only [← Over.comp_left] at e
    rw [comp_lift, comp_lift, ← Category.assoc, hu, Category.comp_id] at e
    exact e
  obtain ⟨u, hu⟩ := exists_unit_of_sq (R := R) a a' (unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := good_exists D.P.isLB (Z := (TK R).left) z
    obtain ⟨J', hJ'⟩ := good_exists D₀.P.isLB (Z := (TK R).left) z
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (va z J J' hJ hJ').symm (va z J J' hJ hJ').symm).trans
      (Eq.trans ?_ ((va' z J J' hJ hJ').trans (gm_pull (𝟙 _) (jK R) z ⊤ trivial a').symm)))
    rw [← hs z J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel)
  refine ⟨scale u σ, scale_isGen u hσ, fun z J J' hJ hJ' => ?_⟩
  refine (gm_scale u σ (toUnit (TK R)).left z _ (hJ.mem _ _)).trans ?_
  have e : gm (toUnit (TK R)).left z ⊤ u = gm (𝟙 (TK R).left) z ⊤ a :=
    (gm_pull (𝟙 _) (jK R) z ⊤ trivial u).symm.trans (congrArg (gm (𝟙 (TK R).left) z ⊤) hu)
  exact (congrArg (· * _) (e.trans (va z J J' hJ hJ').symm)).trans (inv_mul_cancel_right _ _)

theorem exists_zero (D : DegPre R) (T : Over (Sp R)) : ∃ o : GtPt D T, o.IsZero := by
  have H : ∀ χ : D.X, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (DegPre.zeroT D T) χ) DegPre.gtε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J, Good D.P.L z J → val s r z J = val (LB.oneGen D.P.L) r z J :=
    fun χ => exists_gen D.P.isLB (fun U _ h => by
      have e := prod_gt D (𝟙 T) (1 : T ⟶ D.P.A) χ h
      rw [Category.id_comp, _root_.mul_one] at e
      rw [Fintype.prod_empty]
      refine Eq.trans ?_ e.symm
      simp) (LB.oneGen D.P.L) (oneGen_isGen _)
  choose s hs vs using H
  refine ⟨⟨DegPre.zeroT D T, s, hs, corr_of_val D.P.isLB fun y J hJ => vs 0 _ _ y J hJ,
    fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl, fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  rw [vs _ _ _ y J hJ, vs _ _ _ y J hJ, vs _ _ _ y J hJ, val_one, _root_.one_mul, _root_.one_mul]
  refine (val_cub D.cub (𝟙 T) hJ _ _ _).trans ?_
  rw [Category.id_comp (DegPre.zeroT D T)]
  exact (isCub_cubV D.cub hJ).face₃ _ _

theorem exists_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R))
  (β : D₀.toPre.P.A ≅ D.toPre.P.A) (xe : D₀.toPre.X ≃+ D.toPre.X), IsMonHom β.hom →
  (∀ χ, D₀.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) →
  ∀ wΛ : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L)
      ((abelian₂ D.toPre.P.A D.toPre.P.L).pull
        (lift (fst D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) (snd D₀.toPre.P.A D₀.toPre.P.A ≫ β.hom) :
          G2 D₀.toPre.P.A ⟶ G2 D.toPre.P.A).left),
    wΛ.IsGen →
    (∀ (a a' : D₀.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.toPre.P.A.left) → D₀.toPre.P.L.ι), Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val (D₀.toPre.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.toPre.c a) (toUnit (TK R) ≫ D₀.toPre.c a')).left z J J' *
            val (D.toPre.tau (xe a) (xe a')) (𝟙 _) z J) →
  ∀ b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A, padd D.toPre.P.A b b = η[D.toPre.P.A] →
  ∀ w : LB.Iso D₀.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₀.toPre D.toPre β.hom b) GlobalTheory.MumCmp.twε), w.IsGen →
  ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), g.b = b ∧ (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧
    GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D β xe mβ hc wΛ hΛ hτ b hb w₀ hw₀
  have := hR.1.2.2.1
  obtain ⟨w, hw, hn⟩ := exists_normalised hw₀
  have h0 : ∀ (z : (TK R).left) J J', Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' → sv xe w 0 z J J' = 1 :=
    fun z J J' hJ hJ' => sv_zero D₀.tau_bimult D.tau_bimult hJ hJ' (hn _ z J J' hJ hJ')
  have hadd := fun (z : (TK R).left) J J' (hJ : Good D.toPre.P.L z J) (hJ' : Good D₀.toPre.P.L z J') =>
    sv_add D₀.tau_bimult D.tau_bimult hc hw hΛ hJ hJ' (fun a a' => hτ a a' z J J' hJ hJ') (hn _ z J J' hJ hJ')
  have hsq := fun (z : (TK R).left) J J' (hJ : Good D.toPre.P.L z J) (hJ' : Good D₀.toPre.P.L z J') χ =>
    sv_sq D₀.psi_even D.psi_even hc hw hb hJ hJ' (h0 z J J' hJ hJ') χ (hadd z J J' hJ hJ' χ (-χ))
  let E := 𝟙_ (Over (Sp R))
  have H : ∀ χ' : D.toPre.X, ∃ s : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.gtφT D.toPre E b χ') DegPre.gtε), s.IsGen ∧
      ∀ χ, xe χ = χ' → ∀ (z : (TK R).left) J J', Good D.toPre.P.L z J → Good D₀.toPre.P.L z J' →
        val s (toUnit (TK R)).left z J = sv xe w χ z J J' := fun χ' => by
    obtain ⟨χ, rfl⟩ := xe.surjective χ'
    obtain ⟨s, hs, vs⟩ := exists_coord hc hw hb χ (fun z J J' hJ hJ' => hsq z J J' hJ hJ' χ)
    exact ⟨s, hs, fun χ₂ e => by rw [xe.injective e]; exact vs⟩
  choose s hs vs using H
  obtain ⟨z₀⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J', hJ'⟩ := good_exists D₀.toPre.P.isLB z₀
  have red : IsReduced E.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have sep : D.toPre.P.A.left.IsSeparated := by
    have := D.toPre.P.isAb.proper
    exact ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  have hd : ∀ V : E.left.Opens, (V : Set E.left).Nonempty → (toUnit (TK R)).left z₀ ∈ V := TauPull.jK_mem z₀
  have hu : toUnit (TK R) ≫ toUnit E = toUnit (TK R) := toUnit_unique _ _
  have vc : ∀ J, Good D.toPre.P.L z₀ J → ∀ x x' y : E ⟶ D.toPre.P.A,
      val (DegPre.cubAtT D.toPre E x x' y) (toUnit (TK R)).left z₀ J =
        cubV D.toPre.cub z₀ J (toUnit (TK R) ≫ x) (toUnit (TK R) ≫ x') (toUnit (TK R) ≫ y) :=
    fun J hJ x x' y => val_cub D.toPre.cub (toUnit (TK R)) hJ x x' y
  let g : GtPt D.toPre E :=
    { b := b
      s := s
      isGen := hs
      s_zero := TauPull.corr_of_dense D.toPre.P.isLB (toUnit (TK R)).left z₀ hd fun J hJ => by
        rw [vs 0 0 (map_zero xe) z₀ J J' hJ hJ', h0 z₀ J J' hJ hJ', val_one]
      mult := fun χ χ' => TauPull.corr_of_dense D.toPre.P.isLB (toUnit (TK R)).left z₀ hd fun J hJ => by
        obtain ⟨χ, rfl⟩ := xe.surjective χ
        obtain ⟨χ', rfl⟩ := xe.surjective χ'
        refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
        rw [vs _ (χ + χ') (map_add xe χ χ') z₀ J J' hJ hJ', vs _ χ rfl z₀ J J' hJ hJ', vs _ χ' rfl z₀ J J' hJ hJ',
          ← hadd z₀ J J' hJ hJ' χ χ']
        refine congrArg (_ * ·) ((vc J hJ _ _ _).trans ?_)
        rw [← Category.assoc, ← Category.assoc, hu] }
  obtain ⟨o, ho⟩ := exists_zero D.toPre E
  refine ⟨g, rfl, ⟨o, ho, ?_, fun χ => TauPull.corr_of_dense D.toPre.P.isLB (toUnit (TK R)).left z₀ hd fun J hJ => ?_⟩,
    β, xe, mβ, hc, w, hw, fun χ => ?_⟩
  · refine ho.1.trans (Eq.trans ?_ hb.symm)
    rw [DegPre.zeroT, toUnit_unit, Category.id_comp]
  · obtain ⟨χ, rfl⟩ := xe.surjective χ
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [val_corr hJ (ho.2 _), val_one, _root_.one_mul]
    refine (vc J hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vs _ χ rfl z₀ J J' hJ hJ')
      (vs _ χ rfl z₀ J J' hJ hJ')).symm)
    rw [hsq z₀ J J' hJ hJ' χ, ← Category.assoc, hu]
  · obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB
      (φ' := fun i => D₀.toPre.xK χ ≫ twφ D₀.toPre D.toPre β.hom b i) (ε' := fun i => -1 * twε i) (fun U _ h => by
        have e₁ := prod_tw D₀.toPre D.toPre β.hom b (toUnit (TK R) ≫ D₀.toPre.c χ) h
        have e₂ := prod_gt D.toPre (toUnit (TK R)) b (xe χ) h
        rw [Category.assoc, hc] at e₁
        rw [Fintype.prod_sum_type, Fintype.prod_unique]
        simp only [neg_mul, _root_.one_mul, zpow_neg, Finset.prod_inv_distrib]
        refine (congrArg₂ (· * ·) (zpow_neg_one _) e₂).trans (Eq.trans ?_ (congrArg (·⁻¹) e₁).symm)
        show (h (toUnit (TK R) ≫ D.toPre.c (xe χ)).left)⁻¹ * _ = _
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (s (xe χ)) (toUnit (TK R)).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (DVR.pullGen_isGen _ _ _ _ (hs _) _))
    refine ⟨t, mapsAtExp_of_val D.toPre.P.isLB D₀.toPre.P.isLB hw (D₀.toPre.psi_gen χ) ht fun y J J' hJ hJ' => ?_,
      corr_of_val D.toPre.P.isLB fun y J hJ => vt _ _ y J hJ⟩
    refine (vt _ _ y J hJ).trans ((val_mul hJ _ _ _).trans ?_)
    rw [val_pull hJ, Category.id_comp, vs _ χ rfl y J J' hJ hJ', sv, mul_comm, inv_mul_cancel_right, zpow_neg_one]

end GlobalTheory.MumCmp.Point
