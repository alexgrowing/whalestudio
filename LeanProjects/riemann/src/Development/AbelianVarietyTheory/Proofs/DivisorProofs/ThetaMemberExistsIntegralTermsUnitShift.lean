import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointMemberHasLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIsUnitDividingThetaConstantNeZeroDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTranslateThetaSectionUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongrStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.GSep.IntTerm

theorem mem_of_psiCoord {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} (D : DegData V I) {χ : D.toPre.X} (hχ : χ ≠ 0)
    {r : V} (h : Formalism.L2.Pj.PsiCoord D.toPre χ r) : r ∈ I := by
  obtain ⟨j, h₁, h₂, e⟩ := h
  obtain ⟨r', hr', e'⟩ := D.psi_pos χ hχ j ⊤ (isAffineOpen_top _) h₁ h₂
  have e₁ : r' = DegPre.toOpen (R := V) ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e.symm)
  rw [e₁] at hr'
  have hb := GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := V)
  obtain ⟨s, hs, es⟩ := (Ideal.mem_map_iff_of_surjective _ hb.2).1 hr'
  rwa [← hb.1 es]

theorem isUnit_of_sub_mem {V : Type} [CommRing V] [IsLocalRing V] {a b : V} (h : a - b ∈ maximalIdeal V) :
    IsUnit a ↔ IsUnit b := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← mem_nonunits_iff, ← mem_maximalIdeal, ← mem_maximalIdeal]
  exact ⟨fun ha => by simpa using sub_mem ha h, fun hb => by simpa using add_mem h hb⟩

theorem exists_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∃ u : X → C → V, 𝔪.Terms x₀ lab (fun mu c => u mu c * t mu) ∧ (∀ mu, ∃ c, IsUnit (u mu c)) ∧ ∀ c, lab c = x₀ → IsUnit (u 0 c) := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C lab hlab
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega

  have ht0 : IsUnit (t 0) := by
    obtain ⟨u₀, hu₀⟩ := 𝔪.psi 0
    obtain ⟨r₀, hr₀, -, -, hu⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).1
    obtain ⟨v, hv⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).2.1 r₀ _ hr₀ hu₀
    have h1 : IsUnit ((u₀ : V) * t 0) := hv ▸ v.isUnit.mul (hu (map_zero _))
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨x, fr, th, ρ, hx, hfr, hth, hρ, htf⟩ := GlobalTheory.T.exists_points_frames_thetaSection_member I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨hNu, h0, hdv⟩ := GlobalTheory.T.level_isUnit_dividingThetaConstant_ne_zero_dvd I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv
  obtain ⟨w₀, hw₀⟩ := 𝔪.U.ext
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U).1 (FractionRing V) 1 le_rfl w₀ hw₀).1 th
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hdiv V ev X t δ 𝔪

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
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 (by
    have : lab c ∈ Set.range lab := ⟨c, rfl⟩
    rwa [hlab] at this)
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
  have hex : Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_member_has_label I X₁ z₁ act V ev X t δ 𝔪 y hy
    have hmem : a ∈ Set.range lab := by
      rw [hlab]
      exact (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    obtain ⟨c, rfl⟩ := hmem
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  obtain ⟨θ, hθ⟩ := exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi
  choose a ha hau using fun mu c => hκ (gi c) (g' c) (w c) l (hg' c) (hw c) (hif c) (𝔪.e₈ mu) _ (hυ mu)
  have hunit : ∀ mu, ∃ c, IsUnit (a mu c) := fun mu =>
    (GlobalTheory.T.exists_torsionTranslate_thetaSection_unit V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ mu))).imp fun c hc => hau mu c hc
  have hco : ∀ mu c, coef s (g' c) (w c) (𝔪.e₈ mu) =
      l⁻¹ * κ * algebraMap V (FractionRing V) (υ mu * t mu * a mu c) := fun mu c => by
    rw [_root_.mul_assoc, ← ha, inv_mul_cancel_left₀ hl]
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = l⁻¹ * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := GlobalTheory.T.adicSum_fractionField_eq_mul_integral_congr V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * t (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (l⁻¹ * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply]
    rw [_root_.mul_assoc, Units.isUnit_units_mul]
    exact ⟨fun h' => isUnit_of_mul_isUnit_right h', fun h' => ht0.mul h'⟩
  choose S hS hSu using hsum
  have hx₀ : x₀ ∈ Set.range lab := by
    rw [hlab]
    exact AddSubgroup.subset_closure hdiv
  obtain ⟨c₀, rfl⟩ := hx₀
  have hκ0 : l⁻¹ * κ ≠ 0 := left_ne_zero_of_mul (hS c₀ ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c₁, hc₁⟩ := hunit 0
    obtain ⟨r, hr⟩ := hdv (lab c₁)
    rw [hS, hS, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c₁).2 hc₁)
  obtain ⟨σ, hσ⟩ := hS₀
  refine ⟨fun mu c => υ mu * a mu c * σ⁻¹, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs,
    fun c => ⟨htor c, hw c, hlies c⟩, fun mu c => ?_⟩, fun mu => (hunit mu).imp fun c hc => ?_, fun c hc => ?_⟩
  · rw [hco, hS, ← hσ, mul_left_comm, ← map_mul]
    congr 2
    linear_combination (υ mu * a mu c * t mu : V) * σ.inv_mul
  · exact ((υ mu).isUnit.mul hc).mul (σ⁻¹).isUnit
  · have e₁ := hS c
    have e₂ := hS c₀
    simp only [hc] at e₁
    have e := inj (mul_left_cancel₀ hκ0 (e₁.symm.trans e₂))
    exact ((υ 0).isUnit.mul ((hSu c).1 (e ▸ hσ ▸ σ.isUnit))).mul (σ⁻¹).isUnit

end GlobalTheory.GSep.IntTerm
