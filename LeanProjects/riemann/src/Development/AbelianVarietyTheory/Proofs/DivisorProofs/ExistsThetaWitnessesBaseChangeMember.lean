import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.TermsMove

theorem tors_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {g : GtPtF D F} {n : ℕ} (d : ℕ) (h : ∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) :
    ∃ o, GtPtF.IsNsmul (n * d) g o ∧ o.IsZero := by
  letI := @TorusExt.gtGroup
  obtain ⟨o, o₁, o₂⟩ := h
  rw [TorusExt.isNsmul_iff_eq] at o₁
  rw [TorusExt.isZero_iff_eq] at o₂
  refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
  rw [mul_nsmul, ← o₁, o₂, nsmul_zero]

theorem frExt_isGen {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {E : Type} (F : Type) [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] {x : TFK (R := R) E ⟶ A.A} {e : FrAt x} (he : e.IsGen) : (frExt F e).IsGen :=
  pullGen_isGen A.L _ _ e he (TorsionExt.fieldMap (R := R) E F).left

open GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull in
set_option maxHeartbeats 800000 in

theorem exists_witnesses : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C lab x fr th w₀ s g' w h1 h2 h3 h4 h5 h6
    V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen x₂ fr₂ h1' h2' ρ hρ
  have hG := GlobalTheory.globalFns_holds
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  haveI : IsScalarTower (FractionRing V) (FractionRing V) (FractionRing V') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hF : Compat io (FractionRing V') := hf
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := map_maximalIdeal_le io
  have hg₂ : jFK (R := V') (FractionRing V') ≫ spMap f = jFK (R := V) (FractionRing V') := (Spec.map_comp _ _).symm
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w₀₂, hw₀₂, Ω, hΩ₁, hΩ₂, hE⟩ := exists_expand hG hmon hU hF hg₂ hcart.1 hwψ hgen h4 hκ
  obtain ⟨t', s', E', ht', hs'⟩ := (hE 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing V') 𝔪.U.toUnifPre hG h5)
  have hx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = (fieldMap (R := V) (FractionRing V) (FractionRing V') ≫ x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · show _ = (spMap f ≫ (x b).left) ≫ 𝔪.φ
      rw [Category.assoc, ← hφ, ← Category.assoc, h1', Category.assoc, 𝔗.lam_pt, Category.assoc, h1, ← Category.assoc,
        ← Category.assoc, ← spMap_comp, ← spMap_comp, hyK]
    · rw [Category.assoc, hcart.1.w, ← Category.assoc, Over.w, Over.w]
      exact hg₂
  have hfr : ∀ b, FrUp wψ (fr₂ (𝔗.lam b)) (frExt (FractionRing V') (fr b)) (ρ b : FractionRing V') := fun b z J J' hJ hJ' => by
    have e : vS (frExt (FractionRing V') (fr b)) z J = val (fr b) (spMap f) z J :=
      (val_frExt (fr b) (𝟙 _) hJ).trans (congrArg (fun q => val (fr b) q z J) (Category.id_comp _))
    rw [e]
    exact hρ b z J J' hJ hJ'
  have hv : ∀ b, ValAt t' (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b))
      (f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) * ((ρ b)⁻¹ ^ 1).val) := fun b =>
    valAt_pull hΩ₁ hΩ₂ ht' (hx b) (hfr b) (valAt_ext (h3 b))
  have t0 : (show AbSec 𝔪₂.A (FractionRing V') 1 from t') ≠ 0 := fun e => by
    have h₀ := hv x₀
    rw [show t' = (0 : AbSec 𝔪₂.A (FractionRing V') 1) from e] at h₀
    exact mul_ne_zero ((map_ne_zero f).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv))
      (Units.ne_zero _) (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨x', fr', Θ, -, k1, k2, k3, -⟩ := IntTerm.exists_points_frames_theta _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m _ δ 𝔪₂
  obtain rfl : x' = x₂ := funext fun a => Over.OverMorphism.ext (𝔪₂.cart.1.hom_ext ((k1 a).trans (h1' a).symm)
    ((Over.w _).trans (Over.w _).symm))
  have hΘ : ∀ a, ValAt Θ (x' a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩) := fun a z J' hJ' => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' 𝔗.X₂.ρ.P.isLB z
    have e := mul_left_cancel (((k2 a).2 z J J' hJ hJ').trans ((h2' a).2 z J J' hJ hJ').symm)
    have b := k3 a z J' hJ'
    rw [FrameMove.val_powFrame] at b ⊢
    rwa [← e]
  obtain ⟨K, hK⟩ := exists_eq_smul t0 Θ
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') le_rfl w₀₂ hw₀₂
  choose g₁ w₁ a₁ a₂ a₃ a₄ using fun c => exists_ext (F := FractionRing V') hG 𝔪.U h4 (g' c) (h6 c).2.1
  choose g₂ w₂ b₁ b₂ b₃ b₄ using fun c => exists_point hG hI hF hκ hΩ₁ hΩ₂ (fun k hk => (hE k hk).2) (g₁ c) (a₁ c) (ρ (lab c))
  refine ⟨Θ, w₀₂, K • s', g₂, w₂, K, hΘ, hw₀₂, (he' _ _).2 ?_, fun c => ⟨?_, b₁ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e' hK).trans ((map_smul e' K _).trans (congrArg (K • ·) ((he' _ _).1 E')))
  · rw [𝔗.lev]
    exact tors_mul _ (b₂ c _ (a₂ c _ (h6 c).1))
  · exact b₄ c (x' (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c))) _ (frExt (FractionRing V') (fr (lab c)))
      (frExt_isGen _ (h2 (lab c)).1) (hx (lab c)) (hfr (lab c)) (a₄ c (x (lab c)) (fr (lab c)) (h2 (lab c)).1 (h6 c).2.2)
  · rw [coef_smul (b₁ c), _root_.mul_assoc, b₃ c _ _ hs', a₃, he₈]
    rfl
  · have h₀ := valAt_lin (hv b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at h₀
    rw [valAt_unique (hΘ _) h₀, pow_one, _root_.mul_assoc, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end GlobalTheory.TermsMove
