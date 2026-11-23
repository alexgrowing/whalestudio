import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsYy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.TwistModel

section Siegel
variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem twistSum_ofUMem_iff {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)
    (x₀ : X₁.S.Gam) {C : Type} (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (e : ℕ) :
    GlobalTheory.GSep.TwistSum (ofSetup X₁) z₁ _ x₀ (ofUMem 𝔪) lab T sg c τ e ↔
      GlobalTheory.Poinc.Sep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := Iff.rfl

theorem twistAtEach_siegel {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} {sg : ℤˣ}
    (h : GlobalTheory.GSep.TwistAtEach (I := {p : Matrix (Fin 8) (Fin 8) ℤ × Matrix (Fin 8) (Fin 8) ℤ //
      (W + W.transpose) * p.2 = p.1.transpose * (W + W.transpose)}) (ofSetup X₁) z₁ (fun p => act p.1.1) x₀ sg) :
    GlobalTheory.Poinc.Sep.TwistAtEach X₁ z₁ act x₀ sg :=
  fun V _ _ _ ev _ _ _ _ _ 𝔪 C lab hlab T hT c τ hτ => h V ev _ _ _ (ofUMem 𝔪) C lab hlab T hT c τ hτ

end Siegel

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem exists_germ {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z₁) : ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨a, ha⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

theorem exists_germs {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (b : X₁.S.Gam) (e : ℕ) :
    ∃ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ∧
      X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th b / X₁.S.th x₀ := by
  obtain ⟨zt, hz⟩ := exists_germ (z₁ := z₁) (Subalgebra.algebraMap_mem _ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)))
  obtain ⟨h, hh⟩ := exists_germ (z₁ := z₁) (mul_mem (Subalgebra.algebraMap_mem _ (X₁.S.ζ ^ e)) (hd.2 b))
  exact ⟨zt, h, hz, by rw [hh, mul_div_assoc]⟩

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)

theorem exists_yy (mu : X) : ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  have hpow : f p ^ (X₁.S.r * X₁.S.N) = 1 := (hx w hw).1
  let z := pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p)
  have hz : z ^ (X₁.S.r * X₁.S.N) = 1 := by
    simp only [z]
    rw [← map_pow, hpow, map_one]
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg (fun q => q.left) ha
  simp only [Over.comp_left, Over.homMk_left] at e
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK := by
    simp [spMap, jFK, ← Spec.map_comp]
  rw [e2]
  exact e.symm

theorem yK_th_ne_zero {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) : 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

theorem val_stalkHom [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem wt_zero (sg : ℤˣ) (wt : X → ZMod (X₁.S.r * X₁.S.N))
    (hwt : ∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ (0 : X₁.S.Gam) a) (mu : X) : wt mu = 0 := by
  obtain ⟨a, ha⟩ := exists_yy 𝔪 mu
  rw [hwt a mu ha]
  simp [eStd]

theorem twistSum_zero {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) {C : Type} {lab : C → X₁.S.Gam} {T : X → C → V}
    (hT : 𝔪.Terms x₀ lab T) (sg : ℤˣ) (c : C) : GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c 0 0 := by
  intro zt h _ hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hθ := yK_th_ne_zero 𝔪 hd
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hv, -, hexp, hc', hT⟩ := hT
  have hS := (hc' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc' c).2.1 th s _ hexp (hv (lab c))
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : X₁.M.stalkHom z₁ h ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) :=
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ h).2
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩ := by
    rw [← val_stalkHom (ev := ev), 𝔪.yK_eq, 𝔪.yK_eq, ← RatModel.val_mul hsp hO (𝔪.reg _ (X₁.S.th_mem x₀)), hh,
      div_mul_cancel₀ _ hd.1, pow_zero, map_one, _root_.one_mul, add_zero]
  refine TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  rw [hh']
  have e : (fun mu : X => algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) *
      𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) = fun mu => coef s (g' c) (w c) (𝔪.e₈ mu) := by
    funext mu
    rw [wt_zero 𝔪 sg wt hwt mu, ZMod.val_zero, pow_zero, _root_.one_mul, hT]
  rw [e]
  obtain ⟨N, hN, hs, hx, hS⟩ := hS
  refine ⟨N, hN, hs, fun mu => hx _, fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS n
  classical
  refine ⟨S.map 𝔪.e₈.symm.toEquiv.toEmbedding, fun T' hT' => ?_⟩
  have := hS (T'.map 𝔪.e₈.toEquiv.toEmbedding) (fun y hy => by
    refine Finset.mem_map.2 ⟨𝔪.e₈.symm y, hT' (Finset.mem_map.2 ⟨y, hy, rfl⟩), ?_⟩
    simp)
  rw [Finset.sum_map] at this
  exact this

theorem not_twistSum_zero_family {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ) (e : ℕ) :
    ¬ GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 (fun _ : Unit => x₀) (fun _ _ => 0) sg () 0 e := by
  intro H
  haveI : IsLocalHom ev := 𝔪.loc
  obtain ⟨zt, h, hz, hh⟩ := exists_germs hd (x₀ + 0) e
  obtain ⟨N, -, -, -, hS⟩ := H zt h hz hh 0 (fun a mu _ => by simp [eStd])
  obtain ⟨S, hS⟩ := hS 1
  have h1 := hS S le_rfl
  simp only [mul_zero, Finset.sum_const_zero, sub_zero, pow_one] at h1
  have h2 : ev h ∈ maximalIdeal V := by
    have := Submodule.smul_mono le_rfl (le_top : N ≤ ⊤) h1
    simpa using this
  have hpos : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := by
    have := X₁.S.r_pos
    have := X₁.S.N_ge
    positivity
  obtain ⟨u, hu⟩ := (X₁.S.prim.isUnit hpos).pow e
  obtain ⟨k, hk⟩ := exists_germ (z₁ := z₁) (Subalgebra.algebraMap_mem (X₁.M.O z₁) ((u⁻¹ : X₁.o₁ˣ) : X₁.o₁))
  have hinj : Function.Injective (X₁.M.stalkHom z₁) := fun a b hab =>
    (X₁.M.stalkEquiv z₁).injective (Subtype.ext (by rw [RatModel.coe_stalkEquiv, RatModel.coe_stalkEquiv, hab]))
  have hmul : h * k = 1 := hinj (by
    rw [map_mul, hh, hk, add_zero, mul_div_assoc, div_self hd.1, _root_.mul_one, ← hu, ← map_mul, map_one]
    simp)
  exact (mem_maximalIdeal _).1 h2 ((IsUnit.of_mul_eq_one k hmul).map ev)

end GlobalTheory.GSep.TwistModel
