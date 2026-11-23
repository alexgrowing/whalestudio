import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBunStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorMove

theorem isLocalHom_of_finExt {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hi : Algebra.IsIntegral R R' := ⟨fun x => h.2.2.to_isIntegral x⟩
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_TFAE ρ).out 0 4).2 hm

theorem exists_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁] [GrpObj G₂]
    {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {β₁ : G₁.left ⟶ G.left} {β₂ : G₂.left ⟶ G.left}
    {β₁₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {β₂₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (h₁ : IsGrpPullback G₁ G f β₁) (h₂ : IsGrpPullback G₂ G (g ≫ f) β₂)
    (s₁ : Geo.Tor.IsSquare β₁ β₁₂) (s₂ : Geo.Tor.IsSquare β₂ β₂₂) :
    ∃ (β : G₂.left ⟶ G₁.left) (β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left),
      IsGrpPullback G₂ G₁ g β ∧ Geo.Tor.IsSquare β β' ∧ β₂₂ = β' ≫ β₁₂ := by
  have w₀ : β₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f := by rw [h₂.1.w, Category.assoc]
  have e : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ β₁ = β₂ := h₁.1.lift_fst _ _ _
  have w : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ G₁.hom = G₂.hom ≫ g := h₁.1.lift_snd _ _ _
  generalize h₁.1.lift β₂ (G₂.hom ≫ g) w₀ = β at e w
  have s : Geo.Tor.IsSquare β (lift (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))).left :=
    ⟨congrArg (fun q => q.left) (lift_fst (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))),
      congrArg (fun q => q.left) (lift_snd (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂)))⟩
  obtain ⟨β', s⟩ : ∃ β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left, Geo.Tor.IsSquare β β' := ⟨_, s⟩
  refine ⟨β, β', IsGrpPullback.cancel h₁ (h₂.congr rfl e.symm) w, s, ?_⟩
  have a : β₂₂ ≫ (fst G G).left = (β' ≫ β₁₂) ≫ (fst G G).left := by
    rw [s₂.1, Category.assoc, s₁.1, ← Category.assoc, s.1, Category.assoc, e]
  have b : β₂₂ ≫ (snd G G).left = (β' ≫ β₁₂) ≫ (snd G G).left := by
    rw [s₂.2, Category.assoc, s₁.2, ← Category.assoc, s.2, Category.assoc, e]
  exact pullback.hom_ext a b

theorem extLam_congr {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {L : LB ((Over.pullback (jK R)).obj G).left} (hL : L.IsLB) {P Q : LB (G2 G).left} (h : ExtLam G L P) (hQ : Q.IsLB)
    (e : LBIso P Q) : ExtLam G L Q :=
  ⟨hQ, fun κ hκ => LBIso.trans (LB.isLB_linComb hL _ _) (pull_isLB h.1 _) (pull_isLB hQ _) (h.2 κ hκ)
    (GlobalTheory.GenSpread.lbIso_pullback e κ)⟩

theorem exists_finExt_factor_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁
    hρ₁ hβ₁ hsq₁ hgen₁ hext
  haveI := hR.2
  have hR₁ : Base R₁ := ⟨hρ₁.1, charZero_of_injective_ringHom hρ₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)
  obtain ⟨R₂, _, _, _, ρ, hρ, H⟩ := GlobalTheory.T.exists_finiteExtension_trait_uniformisingMumfordBundle R₁ hR₁ G₁ hG₁ A₁ gen₁ hgen₁ _ hext
  have hρ₂ : FinExt (ρ.comp ρ₁) := ⟨hρ.1, hρ.2.1.comp hρ₁.2.1, hρ.2.2.comp hρ₁.2.2⟩
  have hR₂ : Base R₂ := ⟨hρ.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  obtain ⟨D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, β₂, β₂₂, inc₂, pr₂, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    GlobalTheory.FactorPull.factor_baseChange R hR.1 D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr hip hpi R₂ (ρ.comp ρ₁) hρ.1
      hρ₂.2.1 (isLocalHom_of_finExt hρ₂)
  have es : spMap (ρ.comp ρ₁) = spMap ρ ≫ spMap ρ₁ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨β, β', hβ, hsq, hc⟩ := exists_factor hβ₁ (h8.congr es rfl) hsq₁ h9
  obtain ⟨A₂, gen₂, W, _, _, _, φ, GW, _, _, βW, DW, AW, UW, κ, k1, k2, k3, k4, k5, k6, k7, k8⟩ := H G₂ β β' hβ hsq
  have hP := pull_isLB (L := abelian₂ G' U'.LG.L) (LB.isLB_linComb U'.LG.isLB _ _)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have hP₂ := pull_isLB (L := abelian₂ G₂' U₂'.LG.L) (LB.isLB_linComb U₂'.LG.isLB _ _)
    (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ.comp ρ₁, D₂, D₂', F₂, A₂', G₂', inferInstance, inferInstance,
    U₂', oA₂, oG₂, G₂, inferInstance, inferInstance, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, inferInstance, inferInstance,
    inferInstance, φ, GW, inferInstance, inferInstance, βW, DW, AW, UW, κ, hρ₂, hR₂, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    k1, ?_, h10, k3, k4, k5, k6, k7, k8⟩
  exact extLam_congr (pull_isLB A₂.isLB _) k2 hP₂
    (LBIso.trans hP₂ (pull_isLB hP _) k2.1 h10 (GlobalTheory.GenSpread.lbIso_pull_pull hP β' hc)).symm

end GlobalTheory.Mum.FactorMove
