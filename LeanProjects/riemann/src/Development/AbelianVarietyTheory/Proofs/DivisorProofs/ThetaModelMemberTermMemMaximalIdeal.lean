import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTermsIsThetaTermsTorsionFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep.HighTerms

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem exists_integral (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V)
    (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (N : ℕ) (hN : 1 ≤ N) (g' : GtPtF D.toPre (FractionRing V))
    (ho : ∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) :
    ∃ g : GtPt D.toPre (𝟙_ (Over (Sp V))),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' := by
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hkg : N • g' = 0 := by
    obtain ⟨o, h₁, h₂⟩ := ho
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq N g' o).1 h₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq o).1 h₂)
  obtain ⟨n, hn, -⟩ := huniv _ _ (GlobalTheory.Poinc.TorsLift.gtTors_toT g' hkg)
  have hj : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
    Over.homMk (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left) (by
      rw [Category.assoc, Over.w n]
      show _ ≫ jFK (R := V) (FractionRing V) ≫ jK V = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V
      rw [← Category.assoc, hj])
  obtain ⟨s, hs⟩ := GlobalTheory.FinDescent.galoisFixed_point_of_finite V hV.2.1 M hfin nb (fun σ => by
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left = _
    rw [reassoc_of% hσ]; rfl)
  have hns : n = toUnit _ ≫ s := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    refine (congrArg (·.left) hs).trans ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc, hj]
  obtain ⟨g, hg⟩ := GlobalTheory.ConstLie.exists_isPull s g₀
  obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) g
  have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
  rw [← Over.comp_left, ← hns] at h2
  exact ⟨g, by rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hn] at hq⟩

theorem term_mem_maximalIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (mu : Fin 8 → Y1), mu ≠ 0 → T mu c ∈ maximalIdeal V1 := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C₀ lab₀ _ T hT c₁ mu₁ hmu₁
  obtain ⟨x, fr, th, w₀, s, g₀, ω₀, hx, hfr, hth, hw₀, hs, hg₀, hT⟩ := hT
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : IsIntegrallyClosed V := hV.2.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega
  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', k, hk, hNW, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  obtain ⟨hNu, h0, hdv⟩ := GlobalTheory.T.level_unit_thetaConstant_ne_zero_divides_all g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv
  obtain ⟨θ, hθ⟩ := IntTerm.exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi

  have core : ∀ (a : X₁.S.Gam) (gi : GtPt 𝔪.D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
      (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left gi g' →
      (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x a) (fr a) →
      ∀ mu, ∃ α : V, coef s g' w (𝔪.e₈ mu) = k * κ * algebraMap V (FractionRing V) (υ mu * mono W t δ mu * α) ∧
        (IntTerm.UnitAt 𝔪.D.toPre θ (𝔪.D.toPre.c (𝔪.e₈ mu) * gi.b) → IsUnit α) := by
    intro a gi g' w hP ho hw hov mu
    obtain ⟨w', fr', hw', hfr', hov', hco, hval⟩ := Tors.liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
      g' w (x a) (fr a) hw (hfr _).1 hov k hk
    have hb : g'.b = toUnit _ ≫ gi.b := ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 hP).1
    obtain ⟨τ, hτ⟩ := exists_gen_of_local (V := V) 𝔪.D.toPre.P.L 𝔪.D.toPre.P.isLB
      ![(η[𝔪.D.toPre.P.A]).left, gi.b.left] (DegPre.lineε 1)
    obtain ⟨u, hu⟩ := Sep.Frames.frame_unit_core hN gi.b (Sep.Frames.torsion_of_nsmul g' _ hb ho).2 hb w' hw' (by
      obtain ⟨o, h₁, h₂⟩ := ho
      exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hNW _ hN _ o h₁ h₂ _ _ _ hw' hov'
        (hmove _ _ _ _ _ (htf _) hfr' hval)) τ hτ
    have hif : IntTerm.IntFrm 𝔪.D.toPre gi.b w' (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) :=
      ⟨τ, hτ, fun z J hJ => by
        rw [hu z J hJ, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, ← map_mul,
          Units.inv_mul, map_one, map_one, _root_.one_mul]⟩
    obtain ⟨α, hα, hαu⟩ := hκ gi g' w' _ hP hw' hif (𝔪.e₈ mu) _ (hυ mu)
    refine ⟨u * α, ?_, fun h => u.isUnit.mul (hαu h)⟩
    have e : algebraMap V (FractionRing V) u * algebraMap V (FractionRing V) (u⁻¹ : Vˣ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [← hco]
    simp only [map_mul] at hα ⊢
    linear_combination k * algebraMap V (FractionRing V) u * hα - k * coef s g' w' (𝔪.e₈ mu) * e

  let C := ↥(X₁.S.HH X₁.M z₁)
  let lab : C → X₁.S.Gam := Subtype.val
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hdiv V ev X m t δ 𝔪
  have hxb : ∀ (a) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A),
      xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left →
      xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ (x a).left := by
    intro a xb h
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · rw [h, Category.assoc, hx a, ← Category.assoc]
      congr 1
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
    · rw [Category.assoc, Over.w, Over.w]
      change _ = _ ≫ Spec.map (𝟙 _)
      rw [Spec.map_id, Category.comp_id]; rfl
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 c.2
  choose p xb hp hq hxp using hyy
  have hp0 : ∀ c, (p c).y = 0 := fun c => (hp c).trans (map_zero _)
  choose h gi hh hgt hfe hext hpull using fun c => GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN (x (lab c)) (xb c) (p c)
    (hxb _ _ (hxp c)) (hp0 c) (hq c)
  choose g' hg' using fun c => GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) (gi c)
  choose w hw hif hlies using fun c => GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ (x (lab c)) (fr (lab c)) (h c) (gi c)
    (g' c) l hl (hfe c) (hext c) (hg' c) (hlf _ _ _ (htf _) (hh c) (hext c))
  have htor : ∀ c, ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero := fun c => by
    obtain ⟨o, ho, hz⟩ := hgt c
    obtain ⟨o', ho'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) o
    exact ⟨o', GlobalTheory.FieldRestrictionTest.isNsmul_restrict (hg' c) ho' ho,
      GlobalTheory.FieldRestrictionTest.isZero_restrict ho' hz⟩
  have hb : ∀ c, (g' c).b = toUnit _ ≫ (gi c).b := fun c =>
    ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hg' c)).1
  have hex : IntTerm.Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 y hy
    have hmem : a ∈ X₁.S.HH X₁.M z₁ := (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    let c : C := ⟨a, hmem⟩
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  choose a hco hau using fun mu c => core (lab c) (gi c) (g' c) (w c) (hg' c) (htor c) (hw c) (hlies c) mu
  have hunit : ∃ c, IsUnit (a 0 c) :=
    (GlobalTheory.T.exists_torsionTranslate_thetaSection_unit V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ 0))).imp fun c hc => hau 0 c hc
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = k * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * mono W t δ (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (k * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (IntTerm.mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (IntTerm.isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply, IntTerm.mono_zero, _root_.mul_one, Units.isUnit_units_mul]
  choose S hS hSu using hsum
  let c₀ : C := ⟨x₀, AddSubgroup.subset_closure hdiv⟩
  have hS0 : 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem _⟩ = k * κ * algebraMap V (FractionRing V) (S c₀) := hS c₀
  have hκ0 : k * κ ≠ 0 := left_ne_zero_of_mul (hS0 ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c, hc⟩ := hunit
    obtain ⟨r, hr⟩ := hdv (lab c)
    rw [hS, hS0, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c).2 hc)
  obtain ⟨gi₁, hgi₁⟩ := exists_integral V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.U _ hN (g₀ c₁) (hg₀ c₁).1
  obtain ⟨α, hα, -⟩ := core (lab₀ c₁) gi₁ (g₀ c₁) (ω₀ c₁) hgi₁ (hg₀ c₁).1 (hg₀ c₁).2.1 (hg₀ c₁).2.2 mu₁
  have e₁ := hT mu₁ c₁
  rw [hα, hS0, mul_left_comm, ← map_mul] at e₁
  have e₂ := inj (mul_left_cancel₀ hκ0 e₁)
  have hm : T mu₁ c₁ * S c₀ ∈ maximalIdeal V :=
    e₂ ▸ Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (𝔪.mono_mem hmu₁))
  exact (Ideal.mul_unit_mem_iff_mem _ hS₀).1 hm

end GlobalTheory.Poinc.Sep.HighTerms
