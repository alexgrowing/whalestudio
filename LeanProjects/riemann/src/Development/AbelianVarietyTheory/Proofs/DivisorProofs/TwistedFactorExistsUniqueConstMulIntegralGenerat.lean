import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFac

theorem exists_zpow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, fun i j => ?_, fun Z r z J => map_zpow _ _ _⟩
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ => (zpow_mul _ _ _).symm)

theorem exists_norm {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (S₀ ⟶ X)} {ε' : K' → ℤ}
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hF : FormEq (fun k => e ≫ φ k) ε φ' ε')
    (w : LB.Gen (LB.LinComb M φ ε)) (hw : w.IsGen) (v : LB.Gen (LB.LinComb M φ' ε')) (hv : v.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M φ ε), u.IsGen ∧ ∀ y J, Good M y J → val u e y J = val v (𝟙 _) y J := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := φ) (ε' := ε) (fun U _ h => by
      have q := hF U (fun g => h (p ≫ g))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [q, mul_inv_cancel, _root_.mul_one])
    (LB.mulGen M _ _ _ _ w (LB.pullGen M _ _ (LB.mulGen M _ _ _ _ v (LB.invGen M _ _ (LB.pullGen M _ _ w e))) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hv
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hw _))) _))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  rw [vu _ _ y J hJ, val_mul hJ, val_pull hJ, he, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, mul_comm,
    inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R]

theorem tr_left (D : DegPre R) (mu : D.X) :
    (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left =
      (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  refine (lift_snd _ _).trans ?_
  refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
  rw [Category.comp_id]
  exact congrArg (DegPre.prB D (FractionRing R) * ·) (DVR.comp_cP D _ mu).symm

theorem prod_t (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) (n j : ℤ) {T : Over (Sp R)} (y : T ⟶ D.P.A)
    {U : Type} [CommGroup U] (g : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, g (y.left ≫ tφ D a β k) ^ tε n j k = g y.left ^ (n - 1) * g (y * DVR.cP D T β).left *
      (g (DVR.cP D T β).left)⁻¹ * g (1 : T ⟶ D.P.A).left * g (y ≫ a).left ^ j := by
  have e₀ : y.left ≫ tφ D a β 0 = y.left := Category.comp_id _
  have e₁ : y.left ≫ tφ D a β 1 = (y * DVR.cP D T β).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul y (𝟙 _) (DVR.cP D _ β)).trans (by rw [DVR.comp_cP, Category.comp_id]))
  have e₂ : y.left ≫ tφ D a β 2 = (DVR.cP D T β).left := congrArg (fun q => q.left) (DVR.comp_cP D y β)
  have e₃ : y.left ≫ tφ D a β 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) y)
  have e₄ : y.left ≫ tφ D a β 4 = (y ≫ a).left := rfl
  rw [Fin.prod_univ_five, e₀, e₁, e₂, e₃, e₄]
  show _ ^ (n - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ j = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_fac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) [IsMonHom a] (hh : ∀ y, D.c (h y) = D.c y ≫ a)
    (n j : ℤ) (mu β β' : D.X) (w : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) (hw : w.IsGen) :
    ∃ u, IsFac D a h n j mu β β' u := by
  obtain ⟨p₁, h₁, v₁⟩ := exists_zpow (D.psi mu) (D.psi_gen mu) n
  obtain ⟨p₂, h₂, v₂⟩ := exists_zpow (D.psi (h mu)) (D.psi_gen _) j
  obtain ⟨p₃, h₃, v₃⟩ := exists_zpow D.rigK (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) (n + j)
  have z₁ : DegPre.zF D (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := lift_snd _ _
  have z₃ : DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DVR.cP D _ mu := by
    rw [DVR.trF_eq, DVR.tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  obtain ⟨u, hu, vu⟩ := exists_norm D.P.isLB (fst (TF (R := R) (FractionRing R)) D.P.A).left
    (DegPre.zF D (FractionRing R)).left (congrArg (fun q => q.left) z₁) (fun U _ g => by
      have a₁ : ∀ χ, jFK (R := R) (FractionRing R) ≫ ptK (D.c χ) = (DVR.cP D (TF (R := R) (FractionRing R)) χ).left :=
        fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) (FractionRing R) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
          (1 : TF (R := R) (FractionRing R) ⟶ D.P.A).left := (Category.assoc _ _ _).symm
      have q₁ := prod_t D a β' n j (DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R)) g
      have q₂ := prod_t D a β n j
        (DegPre.zF D (FractionRing R) ≫ DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)) g
      have b₁ : (1 : TF (R := R) (FractionRing R) ⟶ D.P.A) ≫ a = 1 := MonObj.one_comp _
      have b₂ : DVR.cP D (TF (R := R) (FractionRing R)) mu ≫ a = DVR.cP D _ (h mu) := by
        rw [DVR.cP, DVR.cP, hh, Category.assoc]
      conv_rhs at q₁ => rw [z₂, b₁, _root_.one_mul]
      conv_rhs at q₂ => rw [z₃, b₂, ← DVR.cPoint_add]
      simp only [Over.comp_left, Category.assoc] at q₁ q₂
      refine (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5) (U := U) _ q₁ (DVR.prod_neg _ _ q₂)).trans ?_
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    w hw (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ p₁ p₂)
      (D.tau mu β)) p₃) (jFK (R := R) (FractionRing R)))
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ h₂) (DVR.tau_isGen D mu β)) h₃) _)
  refine ⟨u, hu, fun z J hJ => (vu z J hJ).trans ((val_pull hJ _ _ _).trans ?_)⟩
  rw [Category.id_comp]
  exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v₁ _ _ _ _) (v₂ _ _ _ _))) rfl)) (v₃ _ _ _ _))

theorem fac_exists_unique_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  intro R _ _ _ _ D a h ha hh n j mu β β' u₀ hu₀
  have hL := D.toPre.P.isLB
  have hs := DVR.surj_appTop D.toPre (FractionRing R) GlobalTheory.globalFns_holds
  obtain ⟨w, hw, vw⟩ := exists_gen hL (φ' := dφ D.toPre a mu β β') (ε' := dε n j) (fun U _ g => by
      refine Finset.prod_congr rfl ?_
      rintro (k | k) -
      · rfl
      · simp only [dφ, Sum.elim_inr]
        rw [← Category.assoc, ← tr_left, Category.assoc])
    (LB.pullGen D.toPre.P.L _ _ u₀ (DegPre.prB D.toPre (FractionRing R)).left) (DVR.pullGen_isGen _ _ _ _ hu₀ _)
  refine ⟨exists_fac D.toPre a h hh n j mu β β' w hw, fun u u' hu hu' => ?_, fun u hu => ?_⟩
  · have z₁ : DegPre.zF D.toPre (FractionRing R) ≫ fst _ _ = 𝟙 _ := lift_fst _ _
    exact gen_unique hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left (DegPre.zF D.toPre (FractionRing R)).left
      (congrArg (fun q => q.left) z₁) hs hu.1 hu'.1 (fun y J hJ => (hu.2 y J hJ).trans (hu'.2 y J hJ).symm)
  · obtain ⟨c, hc⟩ := GlobalTheory.WeilMul.exists_ratio hL (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left hs hu hw
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c, fun Z x z J hJ => ?_⟩
    have e : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom c) = c := Iso.hom_inv_id_apply _ c
    have e₂ := (hc Z x z J hJ).trans ((gs_pull x (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left z ⊤ trivial c).symm)
    rw [vw _ _ z J hJ, val_pull hJ] at e₂
    refine Eq.trans ?_ (congrArg₂ (· * ·) (e₂.trans (congrArg (fun q => gs x z ⊤
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left.appTop.hom q)) e.symm)) rfl)
    rw [← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.TwFac
