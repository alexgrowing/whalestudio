import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyOfTrivialModEpsilon
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Extend

theorem exists_factor {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U} [GrpObj G] [GrpObj G'] [GrpObj A]
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {a : A.left ⟶ G.left} (hb : IsGrpPullback G' G f b)
    (ha : IsGrpPullback A G (j ≫ f) a) : ∃ c : A.left ⟶ G'.left, IsGrpPullback A G' j c ∧ c ≫ b = a := by
  have w : a ≫ G.hom = (A.hom ≫ j) ≫ f := by rw [Category.assoc]; exact ha.1.w
  exact ⟨hb.1.lift _ _ w, hb.cancel (ha.congr rfl (hb.1.lift_fst _ _ w).symm) (hb.1.lift_snd _ _ w),
    hb.1.lift_fst _ _ w⟩

theorem exists_end {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (e₀ : G ⟶ G) (e : A ⟶ A) (h : e.left ≫ c ≫ b = (c ≫ b) ≫ e₀.left) :
    ∃ e' : G' ⟶ G', e'.left ≫ b = b ≫ e₀.left ∧ c ≫ e'.left = e.left ≫ c := by
  have w : (b ≫ e₀.left) ≫ G.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hb.w]
  refine ⟨Over.homMk (hb.lift _ _ w) (hb.lift_snd _ _ w), hb.lift_fst _ _ w, hb.hom_ext ?_ ?_⟩
  · show (c ≫ hb.lift _ _ w) ≫ b = _
    rw [Category.assoc, hb.lift_fst, Category.assoc, h, Category.assoc]
  · show (c ≫ hb.lift _ _ w) ≫ _ = _
    rw [Category.assoc, hb.lift_snd, Category.assoc, hc, ← Category.assoc, Over.w]

theorem exists_sec {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (t : S ⟶ G.left) (ht : t ≫ G.hom = 𝟙 S) (w : U ⟶ A.left)
    (h : w ≫ c ≫ b = (j ≫ f) ≫ t) :
    ∃ s : S' ⟶ G'.left, s ≫ b = f ≫ t ∧ s ≫ G'.hom = 𝟙 S' ∧ ((w ≫ A.hom) ≫ j) ≫ s = w ≫ c := by
  have u : (f ≫ t) ≫ G.hom = 𝟙 S' ≫ f := by rw [Category.assoc, ht, Category.comp_id, Category.id_comp]
  have k : ((w ≫ A.hom) ≫ j) ≫ f = j ≫ f := by
    have := congrArg (· ≫ G.hom) h
    simp only [Category.assoc, ht, Category.comp_id, hb.w, reassoc_of% hc] at this
    simpa only [Category.assoc] using this
  refine ⟨hb.lift _ _ u, hb.lift_fst _ _ u, hb.lift_snd _ _ u, hb.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hb.lift_fst, ← Category.assoc, k, Category.assoc w, h]
  · rw [Category.assoc, hb.lift_snd, Category.comp_id, Category.assoc w c, hc, Category.assoc]

theorem lbIso_of_generic {O Ω : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] (H : Over (Sp O)) [GrpObj H]
    (hH : IsAbelianScheme H) {X : Scheme.{0}} {p : X ⟶ Sp Ω} {c : X ⟶ H.left}
    (hc : IsPullback c p H.hom (spMap (algebraMap O Ω))) {L L' : LB H.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso (L.pull c) (L'.pull c)) : LBIso L L' := by
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have : IsPreimmersion (spMap (algebraMap O Ω)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : Flat (spMap (algebraMap O Ω)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors O))
  have : IsDominant (spMap (algebraMap O Ω)) := by
    obtain ⟨_, _⟩ := (IsGenericPointHom.fractionField O Ω).quasiCompact_and_dominant
    infer_instance
  have : QuasiCompact (spMap (algebraMap O Ω)) := inferInstance
  have := hH.smooth
  have := geometricallyIntegral_of_isAbelianScheme H
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1
    (GlobalTheory.ZH.EndoExtend.pic_ext (spMap (algebraMap O Ω)) hn H (eSec H) (Over.w η[H]) ?_ ?_)
  · rw [GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _),
      GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _)]
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2
      (GenSpread.lbIso_pull_comp hc.isoPullback.inv hc.isoPullback_inv_fst.symm hc.isoPullback_inv_fst.symm h)

end GlobalTheory.Poinc.Extend

open GlobalTheory.Poinc.Extend in

theorem GlobalTheory.Poinc.sameAt_of_generic : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  intro O Ω R₁ R₂ M Γ _ _ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ ⟨P, a₁, a₂, h₁, h₂, l₁, l₂, hE, hx⟩
  have spc : ∀ {R : Type} [CommRing R] (f : R →+* O),
      spMap ((algebraMap O Ω).comp f) = spMap (algebraMap O Ω) ≫ spMap f := fun f => by
    rw [← Spec.map_comp]; rfl
  rw [spc] at h₁ h₂
  simp only [spc] at hx
  obtain ⟨Q₁, b₁, g₁, m₁⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₁.A.left),
      IsGrpPullback Q.A P₁.A (spMap f₁) b ∧ LBIso Q.L (P₁.L.pull b) :=
    ⟨StrictPull.polPull P₁ (spMap f₁), _, isGrpPullback_pullback _ _,
      PolBaseChange.lbIso_refl (pull_isLB P₁.isLB _)⟩
  obtain ⟨Q₂, b₂, g₂⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₂.A.left),
      IsGrpPullback Q.A P₂.A (spMap f₂) b :=
    ⟨StrictPull.polPull P₂ (spMap f₂), _, isGrpPullback_pullback _ _⟩
  obtain ⟨c₁, k₁, rfl⟩ := exists_factor g₁ h₁
  obtain ⟨c₂, k₂, rfl⟩ := exists_factor g₂ h₂
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj : IsGenericPointHom (spMap (algebraMap O Ω)) := IsGenericPointHom.fractionField O Ω
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have s₁ := isSemiAbelian_of_isAbelianScheme Q₁.A Q₁.isAb
  have s₂ := isSemiAbelian_of_isAbelianScheme Q₂.A Q₂.isAb
  have := s₁.smooth
  have := s₂.smooth
  have := s₁.separated
  have := s₂.separated
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₁ s₂ k₁ k₂ (𝟙 P.A)
  obtain ⟨F', ⟨-, eF'⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₂ s₁ k₂ k₁ (𝟙 P.A)
  rw [Over.id_left, Category.id_comp] at eF eF'
  let I : Q₁.A ≅ Q₂.A :=
    ⟨F, F', ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF, ← eF', Over.id_left, Category.comp_id]),
      ExtUnique.over_hom_ext_of_isPullback k₂.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF', ← eF, Over.id_left, Category.comp_id])⟩
  have : IsMonHom I.hom := hF
  have g₂' : IsGrpPullback Q₁.A P₂.A (spMap f₂) (F.left ≫ b₂) :=
    ((isGrpPullback_of_iso I).comp g₂).congr (Category.id_comp _) rfl
  refine ⟨Q₁, b₁, F.left ≫ b₂, g₁, g₂', m₁, ?_, fun E => ?_, fun x => ?_⟩
  · refine lbIso_of_generic Q₁.A Q₁.isAb k₁.1 Q₁.isLB (pull_isLB P₂.isLB _) ?_
    refine LBIso.trans (pull_isLB Q₁.isLB _) (pull_isLB P₁.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _)
      (GenSpread.lbIso_pull_of_lbIso m₁ c₁ rfl) ?_
    refine LBIso.trans (pull_isLB P₁.isLB _) P.isLB (pull_isLB (pull_isLB P₂.isLB _) _) l₁.symm ?_
    exact LBIso.trans P.isLB (pull_isLB P₂.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _) l₂
      (GenSpread.lbIso_pull_pull P₂.isLB c₁ (by rw [eF, Category.assoc]))
  · obtain ⟨e, u₁, u₂⟩ := hE E
    obtain ⟨d₁, v₁, w₁⟩ := exists_end g₁.1 k₁.1.w (e₁ E) e u₁
    obtain ⟨d₂, v₂, w₂⟩ := exists_end g₂.1 k₂.1.w (e₂ E) e u₂
    have : d₁ ≫ F = F ≫ d₂ := ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, w₁, Category.assoc, ← eF, ← Category.assoc, ← eF, w₂])
    refine ⟨d₁, v₁, ?_⟩
    rw [← Category.assoc, ← Over.comp_left, this, Over.comp_left, Category.assoc, v₂, Category.assoc]
  · obtain ⟨w, u₁, u₂⟩ := hx x
    obtain ⟨d₁, v₁, z₁, w₁⟩ := exists_sec g₁.1 k₁.1.w (t₁ x).left (Over.w (t₁ x)) w u₁
    obtain ⟨d₂, v₂, z₂, w₂⟩ := exists_sec g₂.1 k₂.1.w (t₂ x).left (Over.w (t₂ x)) w u₂
    have : Surjective (w ≫ P.A.hom) :=
      ⟨fun y => ⟨y, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
    have : d₁ ≫ F.left = d₂ := ext_of_isDominant_of_isSeparated Q₂.A.hom
      (by rw [Category.assoc, Over.w, z₁, z₂]) ((w ≫ P.A.hom) ≫ spMap (algebraMap O Ω))
      (by rw [← Category.assoc, w₁, w₂, eF, Category.assoc])
    exact ⟨d₁, v₁, by rw [← Category.assoc, this, v₂]⟩
