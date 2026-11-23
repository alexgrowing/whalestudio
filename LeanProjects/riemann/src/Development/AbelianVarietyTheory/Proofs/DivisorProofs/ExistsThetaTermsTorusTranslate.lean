import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTorsionPointsAdditiveLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTranslateLiesOverProductTorsionFraStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  classical
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := K)
  obtain ⟨J₀, hJ₀⟩ := exists_good' A.isLB (z₀ : (TFK (R := R) K).left)
  set u := val e' (𝟙 _) z₀ J₀ * (val e (𝟙 _) z₀ J₀)⁻¹ with hu
  obtain ⟨c, hc⟩ := cstH_surj (R := R) z₀ u.val
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hc
    have h1 : (1 : (TF (R := R) K).left.presheaf.stalk z₀) = 0 := by
      rw [← u.val_inv, ← hc, zero_mul]
    have := cstH_inj (R := R) z₀ (show cstH (R := R) z₀ 1 = cstH (R := R) z₀ 0 by rw [map_one, map_zero]; exact h1)
    exact one_ne_zero this
  · intro z J hJ
    obtain rfl := pt_eq (R := R) (F := K) z z₀
    have h1 := val_tr he' (𝟙 _) hJ hJ₀
    have h2 := val_tr he (𝟙 _) hJ hJ₀
    have hcomm : ∀ (y : (TFK (R := R) K).left) (P a b : ((TFK (R := R) K).left.presheaf.stalk y)ˣ),
        P * a = a * b⁻¹ * (P * b) := by
      intro y P a b
      rw [_root_.mul_comm P b, ← _root_.mul_assoc, inv_mul_cancel_right, _root_.mul_comm]
    have key : val e' (𝟙 _) z J = u * val e (𝟙 _) z J := by
      rw [h1, h2, hu]
      exact hcomm _ _ _ _
    show _ = cstH (R := R) z c * _
    rw [key, Units.val_mul, hc]

theorem over_scale {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' hgen s s' v hexp hval
  obtain ⟨wk, hwkgen, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_pow w hw k
  have hv' : ValAt s x e (c ^ k * v) := by
    intro z J hJ
    rw [hval z J hJ, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, cst_eq, map_mul, map_pow]
    ring
  have hsum := h k hk wk hwk hwkgen s s' (c ^ k * v) hexp hv'
  have hscale : ∀ j, coef s' g' wk' j = c⁻¹ ^ k * coef s' g' wk j := by
    intro j
    refine GlobalTheory.UT.TorsionValue.coef_scale hwkgen (fun z J hJ => ?_) s' j
    rw [hwk' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ]
    simp only [cst_eq, map_pow, mul_pow]
  have := sumF_const_mul (c⁻¹ ^ k) hsum
  have hcv : c⁻¹ ^ k * (c ^ k * v) = v := by
    rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul]
  rw [hcv] at this
  have hf : coef s' g' wk' = fun j => c⁻¹ ^ k * coef s' g' wk j := funext hscale
  rw [hf]
  exact this

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem exists_terms_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : (Fin 8 → X) → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro g n F W Z i X₁ z₁ act x₀ _ V _ _ _ ev X _ m t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hexp, hg', hTc⟩ := hT
  obtain ⟨χ, hχ1, hχ⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨p₀, hp₀y, hg₀⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor 𝔪.D.3 χ hχ1
  obtain ⟨p, xτ, hpy, hpg, hpq, hxτ⟩ := hχ p₀.g hg₀
  have hxadd := GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx (lab c) τ xτ hxτ
  obtain ⟨ρA, hρA, hρfr⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  obtain ⟨hg'o, hwc, hover⟩ := hg' c
  have hadd : (g' c).IsAdd p₀.g (g' c + p₀.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).mpr rfl
  obtain ⟨hb, -⟩ := GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd
  obtain ⟨w₂, hw₂gen, hw₂⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + p₀.g).b, w₂.IsGen ∧
      ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    generalize (g' c + p₀.g).b = b at hb ⊢
    subst hb
    exact ⟨w c, hwc, fun _ _ _ => rfl⟩
  obtain ⟨e₂, he₂t, he₂o⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c))
    (hρfr _) (g' c) (w c) hg'o hwc hover χ hχ1 p₀.g hg₀ p xτ hpy hpg hpq (g' c + p₀.g) hadd w₂ hw₂ (x (lab c + τ)) hxadd
  obtain ⟨κ, hκ0, hκ⟩ := exists_frAt_ratio he₂t.2.1 (hfr (lab c + τ)).1
  obtain ⟨w', hw'gen, hw'⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w₂ hw₂gen (inv_ne_zero hκ0)
  have hover' := over_scale 𝔪 hw₂gen hκ0 hκ hw' he₂o
  have hrN : 0 < X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    rw [hj, X₁.ρ.N_eq]
    have := X₁.ρ.n_prime.pos
    positivity
  have hκpow : κ ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' 𝔪.A.isLB (z₀ : (TFK (R := V) (FractionRing V)).left)
    have h := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (hρfr (lab c + τ)) he₂t hJ₀
    rw [div_self', one_pow] at h
    have hk := hκ z₀ J₀ hJ₀
    apply cstH_inj (R := V) z₀
    rw [map_pow, map_one]
    have hq : (val (fr (lab c + τ)) (𝟙 _) z₀ J₀ / val e₂ (𝟙 _) z₀ J₀).val = cstH (R := V) z₀ κ := by
      rw [div_eq_mul_inv, Units.val_mul, hk, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
      rfl
    rw [← hq, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hint : ∀ mu : Fin 8 → X, ∃ y : V,
      algebraMap V (FractionRing V) y = κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val := by
    intro mu
    have hcl : IsIntegrallyClosed V := 𝔪.cn.2.1
    have h1 : (χ (Multiplicative.ofAdd (𝔪.e₈ mu))) ^ (X₁.S.r * X₁.S.N) = 1 := by
      rw [← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply]
    have hpow : (κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val) ^
        ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N)) = 1 := by
      rw [mul_pow, inv_pow, pow_mul, hκpow, one_pow, inv_one, _root_.one_mul, ← Units.val_pow_eq_pow_val, pow_mul', h1,
        one_pow, Units.val_one]
    have hI : IsIntegral V (κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val) := by
      refine IsIntegral.of_pow (Nat.mul_pos (Nat.mul_pos (pow_pos hrN 2) (pow_pos hrN 2)) hrN) ?_
      rw [hpow]
      exact isIntegral_one
    exact IsIntegrallyClosed.isIntegral_iff.mp hI
  choose y hy using hint
  have hcoef : ∀ mu, coef s (g' c + p₀.g) w' (𝔪.e₈ mu) =
      κ⁻¹ * (χ (Multiplicative.ofAdd (𝔪.e₈ mu))).val * coef s (g' c) (w c) (𝔪.e₈ mu) := by
    intro mu
    refine GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hwc (fun z J hJ => ?_) s (𝔪.e₈ mu)
    rw [hw' z J hJ, hw₂ z J hJ, cst_eq]
  have hg₂o : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c + p₀.g) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := hg'o
    rw [GlobalTheory.TorusExt.isNsmul_iff_eq] at ho
    rw [GlobalTheory.TorusExt.isZero_iff_eq] at hoz
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).mpr ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).mpr rfl⟩
    rw [smul_add, ← ho, hoz, zero_add, GlobalTheory.TorusExt.qk_nsmul 𝔪.D.3 p₀, hp₀y, map_zero]
  refine ⟨fun mu _ => y mu * T mu c, x, fr, th, w₀, s, fun _ => g' c + p₀.g, fun _ => w', hx, hfr, hth, hw₀, hexp,
    fun _ => ⟨hg₂o, hw'gen, hover'⟩, fun mu _ => ?_⟩
  rw [map_mul, hy mu, hcoef mu, ← hTc mu c]
  ring

end GlobalTheory.Poinc.Sep.TermsExt
