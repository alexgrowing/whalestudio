import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.USt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDvrOfCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DenseGlue

open GlobalTheory.PicGlue GlobalTheory.CechPic

theorem cls_pull_comp {P T T' : Scheme.{0}} {W : P.Opens} {L : LB P} (hL : IsOn W L) (g : T ⟶ P)
    (hg : ∀ z, g z ∈ W) (s : T' ⟶ T) {g' : T' ⟶ P} (w : s ≫ g = g') (h : (L.pull g).IsLB)
    (h' : (L.pull g').IsLB) : cls (L.pull g') h' = CechPic.pull s (cls (L.pull g) h) := by
  subst w
  rw [← cls_pull h s (pull_isLB h s)]
  exact ((cls_eq_iff _ _).2 (isOn_pull_comp P _ _ _ L g s hL hg)).symm

theorem exists_rigidify {X P : Scheme.{0}} (p : P ⟶ X) {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {V : X.Opens} {M : LB P}
    (hM : IsOn (p ⁻¹ᵁ V) M) : ∃ M' : LB P, IsOn (p ⁻¹ᵁ V) M' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ P),
      (∀ z, g z ∈ p ⁻¹ᵁ V) → ∀ (h₁ : (M'.pull g).IsLB) (h₂ : (M.pull g).IsLB) (h₃ : (M.pull (g ≫ p ≫ e)).IsLB),
        cls _ h₁ = cls _ h₂ - cls _ h₃ := by
  have hpe := retract_section_apply p e he
  have hι : ∀ z, (p ⁻¹ᵁ V).ι z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
  have hι' : ∀ z, ((p ⁻¹ᵁ V).ι ≫ p ≫ e) z ∈ p ⁻¹ᵁ V := fun z ↦ by
    change p (e (p _)) ∈ V
    rw [hpe]
    exact z.2
  have k₁ := pull_isLB_of_isOn P _ _ M _ hM hι
  have k₂ := pull_isLB_of_isOn P _ _ M _ hM hι'
  obtain ⟨N, hN, hc⟩ := cls_surj (cls _ k₁ - cls _ k₂)
  obtain ⟨M', hM', hi⟩ := exists_isOn_of_openImmersion P _ (p ⁻¹ᵁ V).ι N hN
  rw [Scheme.Opens.opensRange_ι] at hM'
  refine ⟨M', hM', fun T g hg h₁ h₂ h₃ ↦ ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : T ⟶ (p ⁻¹ᵁ V).toScheme, t ≫ (p ⁻¹ᵁ V).ι = g :=
    ⟨IsOpenImmersion.lift (p ⁻¹ᵁ V).ι g (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg z), IsOpenImmersion.lift_fac _ _ _⟩
  have k₃ := pull_isLB_of_isOn P _ _ M' _ hM' hι
  rw [cls_pull_comp hM' _ hι t ht k₃, cls_pull_comp hM _ hι t ht k₁,
    cls_pull_comp hM _ hι' t (by rw [reassoc_of% ht]) k₂, ← map_sub, ← hc, (cls_eq_iff k₃ hN).2 hi]

theorem exists_glue_of_rigid {X P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (U : X.Opens) [IsDominant U.ι] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P}
    (he : e ≫ p = 𝟙 X) {L₀ : LB P} (h₀ : IsOn (p ⁻¹ᵁ U) L₀) (t₀ : ∃ t : LB.Gen (L₀.pull (U.ι ≫ e)), t.IsGen)
    {Ix : Type} (V : Ix → X.Opens) (hV : ∀ y, ∃ i, y ∈ V i) (L : Ix → LB P) (hL : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i))
    (t : ∀ i, ∃ t : LB.Gen ((L i).pull ((V i).ι ≫ e)), t.IsGen)
    (hi : ∀ i, LBIso ((L i).pull (p ⁻¹ᵁ (V i ⊓ U)).ι) (L₀.pull (p ⁻¹ᵁ (V i ⊓ U)).ι)) :
    ∃ N : LB P, N.IsLB ∧ ∀ i, ∃ v : Cmp (p ⁻¹ᵁ V i) N (L i), IsoOn (p ⁻¹ᵁ V i) N (L i) v := by
  have hpe := retract_section_apply p e he
  have hR : ∀ {W : X.Opens} {M : LB P}, IsOn (p ⁻¹ᵁ W) M → (∃ t : LB.Gen (M.pull (W.ι ≫ e)), t.IsGen) →
      ∃ r : RigD e M, RigOn e M r := fun {W M} hM ht ↦
    rigOn_of_triv_open P X e W M (fun a y hy ↦ by
      have : p (e y) ∈ W := hM.le a hy
      rwa [hpe] at this) ht
  obtain ⟨r₀, hr₀⟩ := hR h₀ t₀
  choose r hr using fun i ↦ hR (hL i) (t i)
  have hv : ∀ i, ∃ v : Cmp (p ⁻¹ᵁ (V i ⊓ U)) (L i) L₀, IsoOn _ (L i) L₀ v ∧
      PicGlue.Norm e _ (L i) L₀ v (r i) r₀ := fun i ↦ by
    obtain ⟨w, hw⟩ := isoOn_of_lbIso P _ (L i) L₀ (hi i)
    exact exists_norm P X p e he _ _ _ (L i) L₀ w (r i) r₀ (hL i) h₀ (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr i) hr₀
  choose v hv hn using hv
  obtain ⟨w, hw, hc⟩ := exists_cocycle U p he h₀ r₀ V L hL r v hv hn
  exact lb_glue P Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL hw hc

theorem exists_glue {X P U Q : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (hj : Dense (Set.range j)) (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p]
    {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {a : Q ⟶ P} {π : Q ⟶ U} (sq : IsPullback a π p j) {eU : U ⟶ Q}
    (w : eU ≫ a = j ≫ e) {L : LB Q} (hL : L.IsLB) (hrig : ∃ t : LB.Gen (L.pull eU), t.IsGen)
    (H : ∀ y : X, y ∉ Set.range j → ∃ V : X.Opens, y ∈ V ∧ ∃ M : LB P, IsOn (p ⁻¹ᵁ V) M ∧
      LBIso (M.pull ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a)) (L.pull (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι)) :
    ∃ M : LB P, M.IsLB ∧ LBIso (M.pull a) L := by
  have hpe := retract_section_apply p e he
  have : IsOpenImmersion a := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip ‹_›
  let U₀ : X.Opens := j.opensRange
  have : IsDominant U₀.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hj⟩
  have hD : a.opensRange = p ⁻¹ᵁ U₀ := by
    ext x
    change x ∈ Set.range a ↔ p x ∈ Set.range j
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨π q, by rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩
    · intro hx
      obtain ⟨q, rfl⟩ : x ∈ Set.range (pullback.fst p j) := by
        rw [Scheme.Pullback.range_fst]
        exact hx
      exact ⟨sq.isoPullback.inv q, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_fst]⟩
  obtain ⟨L₀, h₀, i₀⟩ := exists_isOn_of_openImmersion P Q a L hL
  rw [hD] at h₀
  have ha : ∀ z, a z ∈ p ⁻¹ᵁ U₀ := fun z ↦ hD ▸ ⟨z, rfl⟩
  have k₀ := pull_isLB_of_isOn P _ _ L₀ a h₀ ha
  have c₀ : cls _ k₀ = cls L hL := (cls_eq_iff _ _).2 i₀

  have z₀ : ∀ (T : Scheme.{0}) (s : T ⟶ X), (∀ z, s z ∈ U₀) → ∀ h : (L₀.pull (s ≫ e)).IsLB, cls _ h = 0 := by
    intro T s hs h
    let κ := IsOpenImmersion.lift j s (by rintro _ ⟨z, rfl⟩; exact hs z)
    have hκ : κ ≫ j = s := IsOpenImmersion.lift_fac _ _ _
    rw [cls_pull_comp h₀ a ha (κ ≫ eU) (by rw [Category.assoc, w, reassoc_of% hκ]) k₀, c₀, pull_comp,
      ← cls_pull hL eU (pull_isLB hL eU), (cls_eq_zero_iff _).2 hrig, map_zero]
  have hse : ∀ {T : Scheme.{0}} (s : T ⟶ X) {W : X.Opens}, (∀ z, s z ∈ W) → ∀ z, (s ≫ e) z ∈ p ⁻¹ᵁ W :=
    fun s W hs z ↦ by
      change p (e (s z)) ∈ W
      rw [hpe]
      exact hs z
  have t₀ : ∃ t : LB.Gen (L₀.pull (U₀.ι ≫ e)), t.IsGen :=
    (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ L₀ _ h₀ (hse U₀.ι fun z ↦ z.2))).1 (z₀ _ U₀.ι (fun z ↦ z.2) _)
  have key : ∀ o : Option X, ∃ (V : X.Opens) (M : LB P), (∀ y, o = some y → y ∉ U₀ → y ∈ V) ∧
      (o = none → V = U₀ ∧ M = L₀) ∧ IsOn (p ⁻¹ᵁ V) M ∧ (∃ t : LB.Gen (M.pull (V.ι ≫ e)), t.IsGen) ∧
      LBIso (M.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) (L₀.pull (p ⁻¹ᵁ (V ⊓ U₀)).ι) := fun o ↦ by
    by_cases ho : ∃ y, o = some y ∧ y ∉ U₀
    swap
    · have k := pull_isLB_of_isOn P _ _ L₀ (p ⁻¹ᵁ (U₀ ⊓ U₀)).ι h₀ fun z ↦ z.2.1
      exact ⟨U₀, L₀, fun y h h' ↦ (ho ⟨y, h, h'⟩).elim, fun _ ↦ ⟨rfl, rfl⟩, h₀, t₀, (cls_eq_iff k k).1 rfl⟩
    obtain ⟨y, rfl, hy⟩ := ho
    obtain ⟨V, hyV, M, hM, iM⟩ := H y hy
    obtain ⟨M', hM', hc⟩ := exists_rigidify p he hM
    have hb : ∀ z, ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) z ∈ p ⁻¹ᵁ V := fun z ↦ z.2
    have kb := pull_isLB_of_isOn P _ _ M _ hM hb
    have cmp : ∀ (T : Scheme.{0}) (g : T ⟶ P), (∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀)) → ∀ (h₁ : (M.pull g).IsLB)
        (h₂ : (L₀.pull g).IsLB), cls _ h₁ = cls _ h₂ := fun T g hg h₁ h₂ ↦ by
      let t := IsOpenImmersion.lift ((a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a) g (by
        rintro _ ⟨z, rfl⟩
        obtain ⟨q, hq⟩ : g z ∈ a.opensRange := hD ▸ (hg z).2
        exact ⟨⟨q, show a q ∈ p ⁻¹ᵁ V from hq ▸ (hg z).1⟩, hq⟩)
      have ht : t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ a = g := IsOpenImmersion.lift_fac _ _ _
      rw [cls_pull_comp hM _ hb t ht kb, (cls_eq_iff kb (pull_isLB hL _)).2 iM,
        cls_pull_comp h₀ a ha (t ≫ (a ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) (by rw [Category.assoc, ht]) k₀, c₀, pull_comp,
        cls_pull hL]
    refine ⟨V, M', fun y' h _ ↦ by cases h; exact hyV, fun h ↦ (by cases h), hM', ?_, ?_⟩
    · have hs := hse V.ι fun z ↦ z.2
      have k₂ := pull_isLB_of_isOn P _ _ M _ hM hs
      have e₁ : (V.ι ≫ e) ≫ p ≫ e = V.ι ≫ e := by rw [Category.assoc, reassoc_of% he]
      refine (cls_eq_zero_iff (pull_isLB_of_isOn P _ _ M' _ hM' hs)).1 ?_
      rw [hc _ _ hs _ k₂ (e₁.symm ▸ k₂), sub_eq_zero]
      exact (cls_pull_comp hM _ hs (𝟙 _) (by rw [Category.id_comp, e₁]) k₂ _).trans (pull_id _) |>.symm
    · let g := (p ⁻¹ᵁ (V ⊓ U₀)).ι
      have hg : ∀ z, g z ∈ p ⁻¹ᵁ (V ⊓ U₀) := fun z ↦ z.2
      have hg' : ∀ z, ((g ≫ p) ≫ e) z ∈ p ⁻¹ᵁ (V ⊓ U₀) := hse (g ≫ p) hg
      have k₁ := pull_isLB_of_isOn P _ _ M' g hM' fun z ↦ (hg z).1
      have k₂ := pull_isLB_of_isOn P _ _ M g hM fun z ↦ (hg z).1
      have k₃ := pull_isLB_of_isOn P _ _ M _ hM fun z ↦ (hg' z).1
      have k₄ := pull_isLB_of_isOn P _ _ L₀ g h₀ fun z ↦ (hg z).2
      have k₅ := pull_isLB_of_isOn P _ _ L₀ _ h₀ fun z ↦ (hg' z).2
      refine (cls_eq_iff k₁ k₄).1 ?_
      rw [hc _ g (fun z ↦ (hg z).1) k₁ k₂ k₃, cmp _ g hg k₂ k₄]
      exact sub_eq_self.2 ((cmp _ _ hg' k₃ k₅).trans (z₀ _ (g ≫ p) (fun z ↦ (hg z).2) k₅))
  choose V M h₁ h₂ h₃ h₄ h₅ using key
  obtain ⟨N, hN, hv⟩ := exists_glue_of_rigid U₀ p he h₀ t₀ V (fun y ↦ by
    by_cases hy : y ∈ U₀
    · exact ⟨none, (h₂ none rfl).1 ▸ hy⟩
    · exact ⟨some y, h₁ _ y rfl hy⟩) M h₃ h₄ h₅
  obtain ⟨v, hv⟩ := hv none
  have i₁ := lbIso_pull_of_isoOn P Q _ N (M none) v a hv fun z ↦ (h₂ none rfl).1 ▸ ha z
  rw [(h₂ none rfl).2] at i₁
  exact ⟨N, hN, (cls_eq_iff (pull_isLB hN a) hL).1 (((cls_eq_iff _ k₀).2 i₁).trans c₀)⟩

end GlobalTheory.DenseGlue
