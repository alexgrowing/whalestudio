import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpandsFScale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.TermsCompare

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

open GlobalTheory.FieldBaseChange GlobalTheory.ExpFieldCompare in

theorem exists_expandsF_pow {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) : ∃ d : F, d ≠ 0 ∧
    ∀ (k : ℕ) t s, U.ExpandsF F k w' t s → U.ExpandsF F k w t (d ^ k • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB hw' hw
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const GlobalTheory.firstFiveLaws.1.globalFns A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀, (map_ne_zero _).2 hc₀, fun k t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w' (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]

variable {F} in

theorem valAt_congr {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F}
    (h : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J) (H : ValAt t x e c) : ValAt t x e' c := fun z J hJ => by
  refine (H z J hJ).trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, h z J hJ]

variable {F} in

theorem sec_eq_of_valAt (hT : SecTwistSt) {t t' : SecA A F 1} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x} {c : F} (hc : c ≠ 0)
    (H : ValAt t x e c) (H' : ValAt t' x e c) : t = t' := by
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hT R A F 1 le_rfl
  have hq : Subsingleton (Fin (1 ^ A.g)) := by rw [one_pow]; infer_instance
  obtain ⟨i₀⟩ : Nonempty (Fin (1 ^ A.g)) := by rw [one_pow]; infer_instance
  obtain ⟨r, hr, -⟩ := hb t
  obtain ⟨r', hr', -⟩ := hb t'
  simp only [Fintype.sum_subsingleton _ i₀] at hr hr'
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
  have a := (GlobalTheory.ThetaCompare.sval_smul hr x hJ).symm.trans (H z J hJ)
  have a' := (GlobalTheory.ThetaCompare.sval_smul hr' x hJ).symm.trans (H' z J hJ)
  obtain ⟨q, hq'⟩ := CoefBasic.cstH_surj (R := R) z (sA (b i₀) (ptSecT A.A x).left z J)
  have b₁ : CoefBasic.cstH (R := R) z (r i₀) * CoefBasic.cstH (R := R) z q =
      CoefBasic.cstH (R := R) z c * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (powFrame A.A A.L x e (1 : ℕ)) (𝟙 _) z J)).val := by
    rw [hq', ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]; exact a
  have b₂ : CoefBasic.cstH (R := R) z (r' i₀) * CoefBasic.cstH (R := R) z q =
      CoefBasic.cstH (R := R) z c * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (powFrame A.A A.L x e (1 : ℕ)) (𝟙 _) z J)).val := by
    rw [hq', ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]; exact a'
  have q0 : q ≠ 0 := fun h => by
    rw [h, map_zero, mul_zero] at b₁
    exact hc (CoefBasic.cstH_inj z (((Units.mul_left_eq_zero _).1 b₁.symm).trans (map_zero _).symm))
  have e₀ : r i₀ = r' i₀ := by
    have := b₁.trans b₂.symm
    rw [← map_mul, ← map_mul] at this
    exact mul_right_cancel₀ q0 (CoefBasic.cstH_inj z this)
  have e₁ : ∀ j, t.f j = t'.f j := fun j => by
    have := hr j
    have e₂ : r = r' := funext fun i => by rw [Subsingleton.elim i i₀]; exact e₀
    rw [e₂] at this
    exact this.trans (hr' j).symm
  obtain ⟨f, _⟩ := t
  obtain ⟨f', _⟩ := t'
  obtain rfl : f = f' := funext e₁
  rfl

variable {F} in
theorem coef_smul {k : ℕ} (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} (hw : w.IsGen) (c : F) (s : Fam D.toPre F k) (χ) :
    coef (c • s) g w χ = c * coef s g w χ := by
  have h₁ := ((CoefBasic.coef_basic R D.toPre F k g).2.2 w hw).2.1
  have h₂ : coef (0 : Fam D.toPre F k) g w χ = 0 := by
    have := h₁ 0 0 1 χ
    rw [one_smul, add_zero, _root_.one_mul] at this
    exact left_eq_add.1 this
  have := h₁ s 0 c χ
  rwa [add_zero, h₂, add_zero] at this

variable {U F} in

theorem liesOver_change {w₀ w₀' : W0 U} {d : F}
    (hd : ∀ (k : ℕ) t s, U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀' t (d ^ k • s)) {g : GtPtF D.toPre F}
    {w w' : Frm D.toPre F 1 g.b} (hw' : w'.IsGen)
    (hv : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val = cst F z d * (val w' (𝟙 _) z J).val)
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} (he : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J)
    (H : LiesOver U w₀' g w' x e') : LiesOver U w₀ g w x e := by
  intro k hk wk hwk _ s s' v hs hval
  obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w' hw' k
  have a := H k hk W hWv hW s _ v (hd k s s' hs) (valAt_congr he hval)
  have sc := TorsionValue.coef_scale (w' := wk) hW (c := d ^ k) (fun z J hJ => by
    rw [hwk z J hJ, hWv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
  convert a using 1
  funext χ
  rw [sc, coef_smul g hW]

end

theorem terms_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x x' : X₁.S.Gam) (C C' : Type) (lab : C → X₁.S.Gam) (lab' : C' → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x lab T → 𝔪.Terms x' lab' T' → ∀ (c : C) (c' : C'), lab c = lab' c' → ∀ mu, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x, X₁.S.th_mem x⟩ = algebraMap V (FractionRing V) (T' mu c') * 𝔪.yK ⟨X₁.S.th x', X₁.S.th_mem x'⟩ := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ x₀' C C' lab lab' T T' hT hT' c c' hc mu
  obtain ⟨x, fr, th, w₀, s, p, w, hx, hfr, hth, hw₀, hs, hg, hT⟩ := hT
  obtain ⟨x', fr', th', w₀', s', p', w', hx', hfr', hth', hw₀', hs', hg', hT'⟩ := hT'
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (𝔪.cart.1.hom_ext ((hx a).trans (hx' a).symm) ((Over.w (x a)).trans (Over.w (x' a)).symm))
  have hf : ∀ a z J, Good 𝔪.A.L z J → val (fr a) (𝟙 _) z J = val (fr' a) (𝟙 _) z J := fun a z J hJ => by
    obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' X₁.ρ.P.isLB z
    exact mul_left_cancel (((hfr a).2 z J₀ J hJ₀ hJ).trans ((hfr' a).2 z J₀ J hJ₀ hJ).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  obtain rfl : th = th' := sec_eq_of_valAt hL.2.1.secTwist ha (valAt_congr (hf a) (hth a)) (hth' a)
  obtain ⟨d, hd0, hd⟩ := exists_expandsF_pow 𝔪.U.toUnifPre (FractionRing V) hw₀' hw₀
  have hbij := (expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀' hw₀'
  obtain rfl : s' = d ^ 1 • s := (hbij.1 th).unique hs' (hd 1 th s hs)
  obtain ⟨h₁, h₂, h₃⟩ := hg c
  obtain ⟨h₁', h₂', h₃'⟩ := hg' c'
  rw [hT, hT']
  rw [← hc] at h₃'
  obtain ⟨w₁, hw₁, hv₁⟩ := TorsionValue.exists_frm_scale (w' c') h₂' hd0
  have h₄ : LiesOver 𝔪.U.toUnifPre w₀ (p' c') w₁ (x (lab c)) (fr (lab c)) :=
    liesOver_change hd h₂' hv₁ (hf _) h₃'
  obtain ⟨e, ev⟩ := GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk _ _ _ _ _ _ h₁ h₁' h₂ hw₁ (hfr _).1 h₃ h₄
  rw [coef_smul _ h₂', pow_one]
  generalize w c = om at h₂ ev
  generalize p c = q at om h₂ e ev
  subst e
  exact TorsionValue.coef_scale h₂' (fun z J hJ => by rw [ev z J hJ, hv₁ z J hJ]) s _

end GlobalTheory.Poinc.Sep.TermsCompare

end
