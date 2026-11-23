import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslatesCoverSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleExtensionTranslateOpenStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Mum.Spread

open GlobalTheory.CechPic GlobalTheory.PicGlue GlobalTheory.GenericExtend

theorem geometricallyIntegral_open {P X : Scheme.{0}} (p : P ⟶ X) [GeometricallyIntegral p] (V : P.Opens)
    (e : X ⟶ V.toScheme) (he : e ≫ V.ι ≫ p = 𝟙 X) : GeometricallyIntegral (V.ι ≫ p) := by
  refine ⟨fun K _ y Y fst snd h ↦ ?_⟩
  have hb := IsPullback.of_hasPullback p y
  have : IsIntegral (pullback p y) := GeometricallyIntegral.geometrically_isIntegral _ _ _ hb
  let g : Y ⟶ pullback p y := hb.lift (fst ≫ V.ι) snd (by rw [Category.assoc]; exact h.w)
  have hg : g ≫ pullback.snd p y = snd := hb.lift_snd ..
  have hp : IsPullback fst g V.ι (pullback.fst p y) :=
    IsPullback.of_bot (by rw [hg]; exact h) (hb.lift_fst ..).symm hb
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp inferInstance
  let s : Spec (.of K) ⟶ Y := h.lift (y ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.id_comp, Category.comp_id])
  have : Nonempty Y := ⟨s (Classical.arbitrary (PrimeSpectrum K))⟩
  exact isIntegral_of_isOpenImmersion g

theorem exists_pullU_eq {X U P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (j : U ⟶ X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p]
    {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P} (hN : N.IsLB) {eU : U ⟶ pullback p j}
    (w : eU ≫ pullback.fst p j = j ≫ e) (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι), e (j (κ z)) ∈ N.U a →
      gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) = gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ σ : Γ(P, N.U a)ˣ, pullU (pullback.fst p j) _ σ = τ a := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have key : ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hρ y
      (le_antisymm (coheight_apply_le_one p h1) (Order.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  obtain ⟨s, hs⟩ := exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key y ha h1 hy).1
  obtain ⟨s', hs'⟩ := exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key y ha h1 hy).2
  have hm : s * s' = 1 := hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  exact ⟨⟨s, s', hm, (mul_comm _ _).trans hm⟩, Units.ext hs⟩

def restr {P : Scheme.{0}} (V : P.Opens) (N : LB P) : LB V.toScheme :=
  ⟨N.ι, fun a ↦ V.ι ⁻¹ᵁ N.U a, fun a b ↦ pullU V.ι (N.U a ⊓ N.U b) (N.g a b)⟩

theorem gm_restr {P Z : Scheme.{0}} (V : P.Opens) (N : LB P) (r : Z ⟶ V.toScheme) (z : Z) (a b : N.ι)
    (ha : V.ι (r z) ∈ N.U a) (hb : V.ι (r z) ∈ N.U b) :
    gm r z ((restr V N).U a ⊓ (restr V N).U b) ((restr V N).g a b) = gm (r ≫ V.ι) z (N.U a ⊓ N.U b) (N.g a b) :=
  gm_pull r V.ι z (N.U a ⊓ N.U b) ⟨ha, hb⟩ _

theorem coc_along {P Z : Scheme.{0}} {V : P.Opens} {N : LB P} (hN : IsOn V N) (r : Z ⟶ P) (z : Z) (a b c : N.ι)
    (ha : r z ∈ N.U a) (hb : r z ∈ N.U b) (hc : r z ∈ N.U c) :
    gm r z _ (N.g a b) * gm r z _ (N.g b c) = gm r z _ (N.g a c) := by
  rw [gm_eq_stalkMap r z (N.U a ⊓ N.U b) ⟨ha, hb⟩, gm_eq_stalkMap r z (N.U b ⊓ N.U c) ⟨hb, hc⟩,
    gm_eq_stalkMap r z (N.U a ⊓ N.U c) ⟨ha, hc⟩, ← map_mul, hN.coc (r z) a b c ha hb hc]

theorem isLB_restr {P : Scheme.{0}} {V : P.Opens} {N : LB P} (hN : IsOn V N) : (restr V N).IsLB := by
  refine ⟨top_le_iff.1 fun z _ ↦ ?_, fun a ↦ unit_ext fun z hz ↦ ?_, fun a b c ↦ unit_ext fun z hz ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hN.cov z.1 z.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
  · rw [gm_res (𝟙 _) z _ hz, map_one, gm_restr V N (𝟙 _) z a a hz hz]
    exact mul_eq_left.1 (coc_along hN (𝟙 _ ≫ V.ι) z a a a hz hz hz)
  · rw [map_mul, gm_res (𝟙 _) z _ hz, gm_res (𝟙 _) z _ hz, gm_res (𝟙 _) z _ hz, gm_restr V N (𝟙 _) z a b hz.1.1 hz.1.2,
      gm_restr V N (𝟙 _) z b c hz.1.2 hz.2, gm_restr V N (𝟙 _) z a c hz.1.1 hz.2]
    exact coc_along hN (𝟙 _ ≫ V.ι) z a b c hz.1.1 hz.1.2 hz.2

theorem exists_pullU_eq_of_isOn {X U P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (j : U ⟶ X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p]
    {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {V : P.Opens} (hV : ∀ x, e x ∈ V) {N : LB P} (hN : IsOn V N)
    {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e) (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι), e (j (κ z)) ∈ N.U a →
      gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) = gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ σ : Γ(P, N.U a)ˣ, pullU (pullback.fst p j) _ σ = τ a := by
  let e' : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι e (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, hV x⟩, rfl⟩)
  have he' : e' ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  have he'' : e' ≫ V.ι ≫ p = 𝟙 X := by rw [reassoc_of% he', he]
  have := geometricallyIntegral_open p V e' he''
  let J := pullback.fst p j
  let J' := pullback.fst (V.ι ≫ p) j
  let ψ : pullback (V.ι ≫ p) j ⟶ pullback p j :=
    pullback.lift (J' ≫ V.ι) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have hψ : ψ ≫ J = J' ≫ V.ι := pullback.lift_fst _ _ _
  have hψ' : ψ ≫ pullback.snd p j = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hp : IsPullback J' ψ V.ι J :=
    IsPullback.of_bot (by rw [hψ']; exact IsPullback.of_hasPullback _ _) hψ.symm (IsPullback.of_hasPullback p j)
  have : IsOpenImmersion ψ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp inferInstance
  let eU' : U ⟶ pullback (V.ι ≫ p) j := pullback.lift (j ≫ e') (𝟙 U) (by
    rw [Category.assoc, he'', Category.comp_id, Category.id_comp])
  have w' : eU' ≫ J' = j ≫ e' := pullback.lift_fst _ _ _
  have hπ' : eU' ≫ pullback.snd _ _ = 𝟙 U := pullback.lift_snd _ _ _
  have heψ : eU' ≫ ψ = eU := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hψ, reassoc_of% w', he', w]
    · rw [Category.assoc, hψ', hπ', hπ]
  have l₁ : ∀ a, J' ⁻¹ᵁ (restr V N).U a ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ N.U a := fun a ↦ by
    rw [← Scheme.Hom.comp_preimage ψ, hψ]; exact le_rfl
  have l₁' : ∀ a, ψ ⁻¹ᵁ J ⁻¹ᵁ N.U a ≤ J' ⁻¹ᵁ (restr V N).U a := fun a ↦ by
    rw [← Scheme.Hom.comp_preimage ψ, hψ]; exact le_rfl
  have l₂ : ∀ a, e' ⁻¹ᵁ (restr V N).U a ≤ e ⁻¹ᵁ N.U a := fun a ↦ by
    rw [← he']; exact le_rfl
  obtain ⟨σ, hσ⟩ := exists_pullU_eq j (V.ι ≫ p) he'' (isLB_restr hN) w' hπ'
    (τ := fun a ↦ res (l₁ a) (pullU ψ _ (τ a))) (ρ := fun a ↦ res (l₂ a) (ρ a))
    (fun Z r z a b ha hb ↦ by
      rw [gm_res_pullU r ψ z (l₁ a) ha, gm_res_pullU r ψ z (l₁ b) hb, hτ Z (r ≫ ψ) z a b (l₁ a ha) (l₁ b hb),
        gm_restr V N (r ≫ J') z a b ha hb, Category.assoc, Category.assoc, hψ])
    (fun Z κ z a ha ↦ by
      have ha' : (κ ≫ eU') z ∈ J' ⁻¹ᵁ (restr V N).U a := by
        change ((κ ≫ eU') ≫ J') z ∈ (restr V N).U a
        rw [Category.assoc, w']
        exact ha
      rw [gm_res_pullU (κ ≫ eU') ψ z (l₁ a) ha', gm_res (κ ≫ j) z (l₂ a) ha, Category.assoc, heψ]
      exact hρ Z κ z a (l₂ a ha)) a
  have l₃ : N.U a ≤ V.ι ''ᵁ (restr V N).U a := fun x hx ↦ ⟨⟨x, hN.le a hx⟩, hx, rfl⟩
  refine ⟨res l₃ (Glue.extUnit V.ι _ σ), unit_ext fun q hq ↦ ?_⟩
  obtain ⟨q', rfl⟩ : q ∈ Set.range ψ := by
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback hp ⟨J q, hN.le a hq⟩ q rfl
    exact ⟨z, hz⟩
  refine gm_inj ψ q' hq hq ?_
  have hq' : J' q' ∈ (restr V N).U a := l₁' a hq
  rw [gm_pull ψ J q' _ hq, hψ, gm_res (J' ≫ V.ι) q' l₃ hq', Glue.gm_extUnit V.ι _ σ J' q' hq']
  have := congrArg (gm (𝟙 _) q' _) hσ
  rwa [gm_pull (𝟙 _) J' q' _ hq', gm_res_pullU (𝟙 _) ψ q' (l₁ a) hq', Category.id_comp, Category.id_comp] at this

def LocIso {Q P : Scheme.{0}} (J : Q ⟶ P) (N : LB P) (L : LB Q)
    (t : ∀ (k : N.ι) (l : L.ι), Γ(Q, J ⁻¹ᵁ N.U k ⊓ L.U l)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Q) (z : Z) (k k' : N.ι) (l l' : L.ι), J (r z) ∈ N.U k → J (r z) ∈ N.U k' →
    r z ∈ L.U l → r z ∈ L.U l' →
    gm r z _ (t k l) * gm r z _ (L.g l l') = gm (r ≫ J) z _ (N.g k k') * gm r z _ (t k' l')

theorem exists_locIso {Q P : Scheme.{0}} (J : Q ⟶ P) (L : LB Q) (V : P.Opens) (N : LB V.toScheme)
    (h : LBIso (N.pull (pullback.fst V.ι J)) (L.pull (pullback.snd V.ι J))) :
    ∃ t, LocIso J (OpenExt.extLB V.ι N) L t := by
  obtain ⟨w, hw⟩ := LBIso.symm h
  have hw := (isGen_iff w).1 hw
  let a := pullback.fst V.ι J
  let b := pullback.snd V.ι J
  have hab : a ≫ V.ι = b ≫ J := pullback.condition
  have hab' : ∀ y, V.ι (a y) = J (b y) := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hab, Scheme.Hom.comp_apply]
  have mem : ∀ y (k : N.ι), J (b y) ∈ V.ι ''ᵁ N.U k → a y ∈ N.U k := fun y k hy ↦ by
    rw [← hab'] at hy
    exact V.ι.apply_mem_image_iff.1 hy
  have rg : ∀ q (k : N.ι), J q ∈ V.ι ''ᵁ N.U k → ∃ y, b y = q := fun q k ⟨x, _, hx⟩ ↦ by
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x q hx
    exact ⟨z, hz⟩
  have le : ∀ (k : N.ι) (l : L.ι), J ⁻¹ᵁ (OpenExt.extLB V.ι N).U k ⊓ L.U l ≤
      b ''ᵁ ((N.pull a).U (fun _ ↦ k) ⊓ (L.pull b).U (fun _ ↦ l)) := fun k l q hq ↦ by
    obtain ⟨y, rfl⟩ := rg q k hq.1
    exact b.apply_mem_image_iff.2 ⟨mem_pull.2 (mem y k hq.1), mem_pull.2 hq.2⟩
  refine ⟨fun k l ↦ res (le k l) (Glue.extUnit b _ (w.s (fun _ ↦ k, fun _ ↦ l))), ?_⟩
  intro Z r z k k' l l' hk hk' hl hl'
  rw [gm_eq_stalkMap r z _ (show r z ∈ J ⁻¹ᵁ (OpenExt.extLB V.ι N).U k ⊓ L.U l from ⟨hk, hl⟩),
    gm_eq_stalkMap r z _ (show r z ∈ J ⁻¹ᵁ (OpenExt.extLB V.ι N).U k' ⊓ L.U l' from ⟨hk', hl'⟩),
    gm_eq_stalkMap r z (L.U l ⊓ L.U l') ⟨hl, hl'⟩,
    ← gm_pull r J z ((OpenExt.extLB V.ι N).U k ⊓ (OpenExt.extLB V.ι N).U k') ⟨hk, hk'⟩,
    gm_eq_stalkMap r z _ (show r z ∈ J ⁻¹ᵁ ((OpenExt.extLB V.ι N).U k ⊓ (OpenExt.extLB V.ι N).U k') from ⟨hk, hk'⟩),
    ← map_mul, ← map_mul]
  congr 1
  generalize r z = q at hk hk' hl hl'
  obtain ⟨y, rfl⟩ := rg q k hk
  apply Units.map_injective (f := (b.stalkMap y).hom.toMonoidHom)
    (fun u v h ↦ (ConcreteCategory.bijective_of_isIso (b.stalkMap y)).1 h)
  have e₁ : ∀ (k : N.ι) (l : L.ι) (hk : J (b y) ∈ V.ι ''ᵁ N.U k) (hl : b y ∈ L.U l),
      gm b y _ (res (le k l) (Glue.extUnit b _ (w.s (fun _ ↦ k, fun _ ↦ l)))) = gw w (𝟙 _) y k (fun _ ↦ l) := by
    intro k l hk hl
    rw [gm_res b y (le k l) ⟨hk, hl⟩]
    have := Glue.gm_extUnit b _ (w.s (fun _ ↦ k, fun _ ↦ l)) (𝟙 _) y ⟨mem_pull.2 (mem y k hk), mem_pull.2 hl⟩
    rwa [Category.id_comp] at this
  rw [map_mul, map_mul,
    ← gm_eq_stalkMap b y _ (show b y ∈ J ⁻¹ᵁ (OpenExt.extLB V.ι N).U k ⊓ L.U l from ⟨hk, hl⟩),
    ← gm_eq_stalkMap b y _ (show b y ∈ J ⁻¹ᵁ (OpenExt.extLB V.ι N).U k' ⊓ L.U l' from ⟨hk', hl'⟩),
    ← gm_eq_stalkMap b y (L.U l ⊓ L.U l') ⟨hl, hl'⟩,
    ← gm_eq_stalkMap b y _ (show b y ∈ J ⁻¹ᵁ ((OpenExt.extLB V.ι N).U k ⊓ (OpenExt.extLB V.ι N).U k') from ⟨hk, hk'⟩),
    gm_pull b J y ((OpenExt.extLB V.ι N).U k ⊓ (OpenExt.extLB V.ι N).U k') ⟨hk, hk'⟩, ← hab,
    OpenExt.gm_ext_g V.ι N a y k k' (mem y k hk) (mem y k' hk'), e₁ k l hk hl, e₁ k' l' hk' hl',
    hw _ (𝟙 _) y k k' (fun _ ↦ l) (fun _ ↦ l') (mem y k hk) (mem y k' hk') (mem_pull.2 hl) (mem_pull.2 hl'),
    gm_pull_g L b (𝟙 _) y (fun _ ↦ l) (fun _ ↦ l') (mem_pull.2 hl) (mem_pull.2 hl'), Category.id_comp,
    Category.id_comp, mul_right_comm, inv_mul_cancel_right]

theorem exists_locIso_normalised {Q P U : Scheme.{0}} {J : Q ⟶ P} {N : LB P} {L : LB Q} {π : Q ⟶ U} {eU : U ⟶ Q}
    (hπ : eU ≫ π = 𝟙 U) {t : ∀ (k : N.ι) (l : L.ι), Γ(Q, J ⁻¹ᵁ N.U k ⊓ L.U l)ˣ} (ht : LocIso J N L t)
    (k₀ : N.ι) (l₀ : L.ι) (h₀ : ⊤ ≤ eU ⁻¹ᵁ (J ⁻¹ᵁ N.U k₀ ⊓ L.U l₀)) :
    ∃ t', LocIso J N L t' ∧ ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z), gm (κ ≫ eU) z _ (t' k₀ l₀) = 1 := by
  let v : Γ(U, ⊤)ˣ := (res h₀ (pullU eU _ (t k₀ l₀)))⁻¹
  have hl : ∀ k l, J ⁻¹ᵁ N.U k ⊓ L.U l ≤ π ⁻¹ᵁ ⊤ := fun _ _ _ _ ↦ trivial
  refine ⟨fun k l ↦ res (hl k l) (pullU π ⊤ v) * t k l, fun Z r z k k' l l' hk hk' h h' ↦ ?_, fun Z κ z ↦ ?_⟩
  · rw [map_mul, map_mul, gm_res_pullU r π z (hl k l) ⟨hk, h⟩, gm_res_pullU r π z (hl k' l') ⟨hk', h'⟩,
      _root_.mul_assoc, ht Z r z k k' l l' hk hk' h h', mul_left_comm]
  · rw [map_mul, gm_res_pullU (κ ≫ eU) π z (hl k₀ l₀) (h₀ (x := κ z) trivial), Category.assoc, hπ, Category.comp_id,
      map_inv, gm_res_pullU κ eU z h₀ trivial, inv_mul_cancel]

theorem exists_quot {Q P : Scheme.{0}} {J : Q ⟶ P} {N N' : LB P} {L : LB Q} (hL : L.IsLB) {V V' : P.Opens}
    (hN : IsOn V N) (hN' : IsOn V' N')
    {t : ∀ (k : N.ι) (l : L.ι), Γ(Q, J ⁻¹ᵁ N.U k ⊓ L.U l)ˣ} (ht : LocIso J N L t)
    {t' : ∀ (k : N'.ι) (l : L.ι), Γ(Q, J ⁻¹ᵁ N'.U k ⊓ L.U l)ˣ} (ht' : LocIso J N' L t') (k : N.ι) (k' : N'.ι) :
    ∃ τ : Γ(Q, J ⁻¹ᵁ (N.U k ⊓ N'.U k'))ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Q) (z : Z) (l : L.ι), J (r z) ∈ N.U k →
      J (r z) ∈ N'.U k' → r z ∈ L.U l → gm r z _ τ = gm r z _ (t k l) * (gm r z _ (t' k' l))⁻¹ := by
  have l₁ : ∀ l, J ⁻¹ᵁ (N.U k ⊓ N'.U k') ⊓ L.U l ≤ J ⁻¹ᵁ N.U k ⊓ L.U l := fun l q hq ↦ ⟨hq.1.1, hq.2⟩
  have l₂ : ∀ l, J ⁻¹ᵁ (N.U k ⊓ N'.U k') ⊓ L.U l ≤ J ⁻¹ᵁ N'.U k' ⊓ L.U l := fun l q hq ↦ ⟨hq.1.2, hq.2⟩
  have val : ∀ (Z : Scheme.{0}) (r : Z ⟶ Q) (z : Z) (l : L.ι), r z ∈ J ⁻¹ᵁ (N.U k ⊓ N'.U k') ⊓ L.U l →
      gm r z _ (res (l₁ l) (t k l) * (res (l₂ l) (t' k' l))⁻¹) = gm r z _ (t k l) * (gm r z _ (t' k' l))⁻¹ :=
    fun Z r z l h ↦ by rw [map_mul, map_inv, gm_res r z _ h, gm_res r z _ h]
  obtain ⟨τ, hτ⟩ := glue_unit (J ⁻¹ᵁ (N.U k ⊓ N'.U k')) (fun l ↦ J ⁻¹ᵁ (N.U k ⊓ N'.U k') ⊓ L.U l)
    (fun _ ↦ inf_le_left) (fun q hq ↦ by
      obtain ⟨l, hl⟩ := exists_chart hL q
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hq, hl⟩)
    (fun l ↦ res (l₁ l) (t k l) * (res (l₂ l) (t' k' l))⁻¹) fun l l' q hq ↦ by
      rw [val _ _ q l hq.1, val _ _ q l' hq.2]
      have a := ht _ (𝟙 Q) q k k l l' hq.1.1.1 hq.1.1.1 hq.1.2 hq.2.2
      have b := ht' _ (𝟙 Q) q k' k' l l' hq.1.1.2 hq.1.1.2 hq.1.2 hq.2.2
      rw [mul_eq_left.1 (coc_along hN (𝟙 Q ≫ J) q k k k hq.1.1.1 hq.1.1.1 hq.1.1.1), _root_.one_mul] at a
      rw [mul_eq_left.1 (coc_along hN' (𝟙 Q ≫ J) q k' k' k' hq.1.1.2 hq.1.1.2 hq.1.1.2), _root_.one_mul] at b
      rw [← a, ← b, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]
  refine ⟨τ, fun Z r z l h h' hl ↦ ?_⟩
  have hm : r z ∈ J ⁻¹ᵁ (N.U k ⊓ N'.U k') ⊓ L.U l := ⟨⟨h, h'⟩, hl⟩
  rw [← val Z r z l hm, ← hτ l, gm_res r z _ hm]

theorem isOn_div {P : Scheme.{0}} {N N' : LB P} {V V' : P.Opens} (hN : IsOn V N) (hN' : IsOn V' N') :
    IsOn (V ⊓ V') (LB.div N N') where
  le a := inf_le_inf (hN.le a.1) (hN'.le a.2)
  cov x hx := by
    obtain ⟨a, ha⟩ := hN.cov x hx.1
    obtain ⟨b, hb⟩ := hN'.cov x hx.2
    exact ⟨(a, b), ha, hb⟩
  coc x a b c ha hb hc := by
    rw [gm_div' N N' (𝟙 P) x a b ha hb, gm_div' N N' (𝟙 P) x b c hb hc, gm_div' N N' (𝟙 P) x a c ha hc,
      ← hN.coc x a.1 b.1 c.1 ha.1 hb.1 hc.1, ← hN'.coc x a.2 b.2 c.2 ha.2 hb.2 hc.2, mul_inv,
      _root_.mul_mul_mul_comm]

theorem exists_lb_of_quot {Q P : Scheme.{0}} {J : Q ⟶ P} (hJ : ∀ W, Function.Injective (J.app W).hom) {L : LB Q}
    (hL : L.IsLB) {C : Type} (W : C → P.Opens) (hW : ∀ x, ∃ c, x ∈ W c) (t : ∀ c l, Γ(Q, J ⁻¹ᵁ W c ⊓ L.U l)ˣ)
    (ht : ∀ q c l l', J q ∈ W c → q ∈ L.U l → q ∈ L.U l' →
      gm (𝟙 Q) q _ (t c l) * gm (𝟙 Q) q _ (L.g l l') = gm (𝟙 Q) q _ (t c l'))
    (g : ∀ c d, Γ(P, W c ⊓ W d)ˣ)
    (hg : ∀ q c d l, J q ∈ W c → J q ∈ W d → q ∈ L.U l →
      gm J q _ (g c d) = gm (𝟙 Q) q _ (t c l) * (gm (𝟙 Q) q _ (t d l))⁻¹) :
    ∃ L' : LB P, L'.IsLB ∧ LBIso L (L'.pull J) := by
  have ext : ∀ (A : P.Opens) (u v : Γ(P, A)ˣ), (∀ q, J q ∈ A → gm J q A u = gm J q A v) → u = v := by
    intro A u v h
    refine Units.map_injective (f := (J.app A).hom.toMonoidHom) (hJ A) ?_
    change pullU J A u = pullU J A v
    refine unit_ext fun q hq ↦ ?_
    rw [gm_pull (𝟙 Q) J q A hq, gm_pull (𝟙 Q) J q A hq, Category.id_comp]
    exact h q hq
  let L' : LB P := ⟨C, W, g⟩
  have le : ∀ c l, (L'.pull J).U (fun _ ↦ c) ⊓ L.U l ≤ J ⁻¹ᵁ W c ⊓ L.U l := fun c l q hq ↦ ⟨mem_pull.1 hq.1, hq.2⟩
  refine ⟨L', ⟨top_le_iff.1 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hW x), fun c ↦ ext _ _ _ fun q hq ↦ ?_,
    fun c d f ↦ ext _ _ _ fun q hq ↦ ?_⟩, ⟨fun p ↦ res (le (p.1 PUnit.unit) p.2) (t (p.1 PUnit.unit) p.2)⟩, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hL q
    rw [gm_res J q _ hq, map_one]
    exact (hg q c c l hq hq hl).trans (mul_inv_cancel _)
  · obtain ⟨l, hl⟩ := exists_chart hL q
    rw [map_mul, gm_res J q _ hq, gm_res J q _ hq, gm_res J q _ hq]
    refine (congrArg₂ (· * ·) (hg q c d l hq.1.1 hq.1.2 hl) (hg q d f l hq.1.2 hq.2 hl)).trans
      (Eq.trans ?_ (hg q c f l hq.1.1 hq.2 hl).symm)
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  · refine (isGen_iff_germ _).2 ?_
    rintro q ⟨c, l⟩ ⟨d, l'⟩ hc hd
    have hc' := mem_pull.1 hc.1
    have hd' := mem_pull.1 hd.1
    refine (gm_res (𝟙 Q) q (le (c PUnit.unit) l) hc _).trans (Eq.symm ((congrArg₂ (· * ·)
      ((gm_div' (L'.pull J) L (𝟙 Q) q (c, l) (d, l') hc hd).trans (congrArg (· * _)
        (gm_pull_g L' J (𝟙 Q) q c d hc.1 hd.1))) (gm_res (𝟙 Q) q (le (d PUnit.unit) l') hd _)).trans ?_))
    rw [Category.id_comp]
    refine (congrArg₂ (fun a b ↦ a * _ * b) (hg q _ _ l hc' hd' hc.2) (ht q _ l l' hd' hc.2 hd.2).symm).trans ?_
    have key : ∀ {G : Type} [CommGroup G] (a c g : G), a * c⁻¹ * g⁻¹ * (c * g) = a := fun a c g ↦ by
      rw [_root_.mul_assoc a, _root_.mul_assoc a, ← mul_inv, inv_mul_cancel, _root_.mul_one]
    exact key _ _ _

theorem exists_extension_of_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (P : Scheme.{0}) (p : P ⟶ Sp R) [Smooth p] [GeometricallyIntegral p] (e : Sp R ⟶ P), e ≫ p = 𝟙 _ → ∀ L : LB (pullback p (jK R)), L.IsLB → (∀ x : P, ∃ V : P.Opens, x ∈ V ∧ e (closedPoint R) ∈ V ∧ ∃ N : LB V.toScheme, N.IsLB ∧ LBIso (N.pull (pullback.fst V.ι (pullback.fst p (jK R)))) (L.pull (pullback.snd V.ι (pullback.fst p (jK R))))) → ∃ L' : LB P, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst p (jK R))) := by
  intro R _ _ _ _ _ P p _ _ e he L hL h
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  have : QuasiCompact (jK R) := inferInstance
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hJ := (pullback.fst p (jK R)).app_injective
  have all : ∀ A : P.Opens, e (closedPoint R) ∈ A → ∀ x, e x ∈ A := fun A hA x ↦
    ((IsLocalRing.specializes_closedPoint x).map e.continuous).mem_open A.isOpen hA
  let J := pullback.fst p (jK R)
  let eU : Sp (FractionRing R) ⟶ pullback p (jK R) := pullback.lift (jK R ≫ e) (𝟙 _) (by simp [he])
  have w : eU ≫ J = jK R ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd p (jK R) = 𝟙 _ := pullback.lift_snd _ _ _
  have hw : ∀ x, J (eU x) = e (jK R x) := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  obtain ⟨l₀, hl₀⟩ := exists_chart hL (eU (closedPoint (FractionRing R)))
  have hl₀' : ∀ x, eU x ∈ L.U l₀ := fun x ↦ by rwa [Subsingleton.elim x (closedPoint (FractionRing R))]
  have H : ∀ x : P, ∃ (V : P.Opens) (N : LB P) (t : _) (k₀ : N.ι), x ∈ V ∧ IsOn V N ∧ LocIso J N L t ∧
      (∀ y, e y ∈ N.U k₀) ∧ ∀ (Z : Scheme.{0}) (κ : Z ⟶ Sp (FractionRing R)) (z : Z),
        gm (κ ≫ eU) z _ (t k₀ l₀) = 1 := fun x ↦ by
    obtain ⟨V, hx, hV, N, hN, hiso⟩ := h x
    have hon := OpenExt.isOn_extLB V.ι N hN
    rw [Scheme.Opens.opensRange_ι] at hon
    obtain ⟨t, ht⟩ := exists_locIso J L V N hiso
    obtain ⟨k₀, hk₀⟩ := hon.cov _ hV
    obtain ⟨t', ht', hn⟩ := exists_locIso_normalised hπ ht k₀ l₀ fun y _ ↦
      ⟨show J (eU y) ∈ _ from hw y ▸ all _ hk₀ _, hl₀' y⟩
    exact ⟨V, _, t', k₀, hx, hon, ht', all _ hk₀, hn⟩
  choose V N t k₀ hx hN ht hk₀ hn using H
  have val : ∀ (x : P) (k : (N x).ι) (Z : Scheme.{0}) (κ : Z ⟶ Sp (FractionRing R)) (z : Z),
      e (jK R (κ z)) ∈ (N x).U k → gm (κ ≫ eU) z _ (t x k l₀) = gm (κ ≫ jK R ≫ e) z _ ((N x).g k (k₀ x)) := by
    intro x k Z κ z hk
    have := ht x Z (κ ≫ eU) z k (k₀ x) l₀ l₀ (show J (eU (κ z)) ∈ _ from hw _ ▸ hk)
      (show J (eU (κ z)) ∈ _ from hw _ ▸ hk₀ x _) (hl₀' _) (hl₀' _)
    rwa [gm_self hL (κ ≫ eU) z (hl₀' _), hn, _root_.mul_one, _root_.mul_one, Category.assoc, w] at this
  choose τ hτ using fun x y k k' ↦ exists_quot hL (hN x) (hN y) (ht x) (ht y) k k'
  have ext : ∀ (x y : P) (a : (LB.div (N x) (N y)).ι), ∃ σ : Γ(P, (LB.div (N x) (N y)).U a)ˣ,
      pullU J _ σ = τ x y a.1 a.2 := by
    intro x y
    have l₁ : ∀ a : (N x).ι × (N y).ι, e ⁻¹ᵁ ((N x).U a.1 ⊓ (N y).U a.2) ≤ e ⁻¹ᵁ ((N x).U a.1 ⊓ (N x).U (k₀ x)) :=
      fun a s hs ↦ ⟨hs.1, hk₀ x s⟩
    have l₂ : ∀ a : (N x).ι × (N y).ι, e ⁻¹ᵁ ((N x).U a.1 ⊓ (N y).U a.2) ≤ e ⁻¹ᵁ ((N y).U a.2 ⊓ (N y).U (k₀ y)) :=
      fun a s hs ↦ ⟨hs.2, hk₀ y s⟩
    refine exists_pullU_eq_of_isOn (jK R) p he (V := V x ⊓ V y)
      (fun s ↦ ⟨(hN x).le _ (hk₀ x s), (hN y).le _ (hk₀ y s)⟩) (isOn_div (hN x) (hN y)) w hπ
      (τ := fun a ↦ τ x y a.1 a.2)
      (ρ := fun a ↦ res (l₁ a) (pullU e _ ((N x).g a.1 (k₀ x))) * (res (l₂ a) (pullU e _ ((N y).g a.2 (k₀ y))))⁻¹)
      (fun Z r z a b ha hb ↦ ?_) (fun Z κ z a ha ↦ ?_)
    · obtain ⟨l, hl⟩ := exists_chart hL (r z)
      have e₁ := ht x Z r z a.1 b.1 l l ha.1 hb.1 hl hl
      have e₂ := ht y Z r z a.2 b.2 l l ha.2 hb.2 hl hl
      rw [gm_self hL r z hl, _root_.mul_one] at e₁ e₂
      refine (hτ x y a.1 a.2 Z r z l ha.1 ha.2 hl).trans (Eq.symm ((congrArg₂ (· * ·)
        (gm_div' (N x) (N y) (r ≫ J) z a b ha hb) (hτ x y b.1 b.2 Z r z l hb.1 hb.2 hl)).trans ?_))
      rw [e₁, e₂, mul_inv, _root_.mul_mul_mul_comm]
    · have ha' : J ((κ ≫ eU) z) ∈ (N x).U a.1 ⊓ (N y).U a.2 := show J (eU (κ z)) ∈ _ from hw _ ▸ ha
      refine (hτ x y a.1 a.2 Z (κ ≫ eU) z l₀ ha'.1 ha'.2 (hl₀' _)).trans ?_
      rw [val x a.1 Z κ z ha.1, val y a.2 Z κ z ha.2]
      refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ((map_inv _ _).trans (congrArg (·⁻¹) ?_))))
      · exact (gm_res_pullU (κ ≫ jK R) e z (l₁ a) ha _).trans (by rw [Category.assoc])
      · exact (gm_res_pullU (κ ≫ jK R) e z (l₂ a) ha _).trans (by rw [Category.assoc])
  choose σ hσ using ext
  refine exists_lb_of_quot hJ hL (C := Σ x, (N x).ι) (fun c ↦ (N c.1).U c.2)
    (fun x ↦ ((hN x).cov x (hx x)).elim fun k hk ↦ ⟨⟨x, k⟩, hk⟩) (fun c l ↦ t c.1 c.2 l)
    (fun q c l l' hc hl hl' ↦ ?_) (fun c d ↦ σ c.1 d.1 (c.2, d.2)) fun q c d l hc hd hl ↦ ?_
  · have := ht c.1 _ (𝟙 _) q c.2 c.2 l l' hc hc hl hl'
    rwa [mul_eq_left.1 (coc_along (hN c.1) (𝟙 _ ≫ J) q c.2 c.2 c.2 hc hc hc), _root_.one_mul] at this
  · refine Eq.trans ?_ (hτ c.1 d.1 c.2 d.2 _ (𝟙 _) q l hc hd hl)
    have := congrArg (gm (𝟙 _) q _) (hσ c.1 d.1 (c.2, d.2))
    rw [gm_pull (𝟙 _) J q _ (show J q ∈ (LB.div (N c.1) (N d.1)).U (c.2, d.2) from ⟨hc, hd⟩),
      Category.id_comp] at this
    exact this

end GlobalTheory.Mum.Spread

namespace GlobalTheory.Mum

theorem lb_extends_of_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left), L.IsLB → ExtLam G L PP → ∀ (O : G.left.Opens), (∀ g : G.left, G.hom g = closedPoint R → g ∈ O) → ∀ N : LB O.toScheme, N.IsLB → LBIso (N.pull (pullback.fst O.ι (pullback.fst G.hom (jK R)))) (L.pull (pullback.snd O.ι (pullback.fst G.hom (jK R)))) → ∃ L' : LB G.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ hR G _ _ hG L PP hL hPP O hO N hN hiso
  have := hR.1
  have := hR.2.2.1
  have := hG.smooth
  have := hG.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  refine Spread.exists_extension_of_cover R G.left G.hom (eSec G) (Over.w η[G]) L hL fun x ↦ ?_
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_section_translates_cover_semiAbelian R hR G hG O hO x
  refine ⟨(𝟙 G * (toUnit G ≫ a)).left ⁻¹ᵁ O, ha, hO _ ?_, GlobalTheory.T.exists_bundle_extension_translate_open R G L PP hL hPP O N hN hiso a⟩
  have h₁ : eSec G ≫ (𝟙 G * (toUnit G ≫ a)).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w η[G]
  exact congrArg (fun q : Sp R ⟶ Sp R ↦ q (closedPoint R)) h₁

end GlobalTheory.Mum
