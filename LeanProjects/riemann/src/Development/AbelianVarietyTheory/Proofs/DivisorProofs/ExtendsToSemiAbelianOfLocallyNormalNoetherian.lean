import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.ExtGlue

open GlobalTheory.GroupGlue

theorem exists_scheme_two {Y Y₀ Y₁ Y₂ : Scheme.{0}} {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] {q₁ : Y₀ ⟶ Y₁} {q₂ : Y₀ ⟶ Y₂} (hq : IsPullback q₁ q₂ f₁ f₂)
    {G₁ : Over Y₁} {G₂ : Over Y₂} {G₀ : Over Y₀} {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left}
    (h₁ : IsPullback φ₁ G₀.hom G₁.hom q₁) (h₂ : IsPullback φ₂ G₀.hom G₂.hom q₂) :
    ∃ (G : Over Y) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsPullback ψ₁ G₁.hom G.hom f₁ ∧
      IsPullback ψ₂ G₂.hom G.hom f₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  have : IsOpenImmersion q₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq.flip inferInstance
  have : IsOpenImmersion q₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hq inferInstance
  have : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁.flip inferInstance
  have : IsOpenImmersion φ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂.flip inferInstance
  have : IsOpenImmersion (pushout.inl φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.left))
  have : IsOpenImmersion (pushout.inr φ₁ φ₂) :=
    inferInstanceAs (IsOpenImmersion (colimit.ι (span φ₁ φ₂) WalkingSpan.right))
  have hc : ∀ z : (pushout φ₁ φ₂ : Scheme.{0}),
      z ∈ Set.range (pushout.inl φ₁ φ₂) ∨ z ∈ Set.range (pushout.inr φ₁ φ₂) := by
    intro z
    obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span φ₁ φ₂) z
    rcases i with _ | _ | _
    · refine Or.inl ⟨φ₁ x, Eq.trans ?_ hx⟩
      exact congrArg (fun g => g x) (colimit.w (span φ₁ φ₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨x, hx⟩
    · exact Or.inr ⟨x, hx⟩
  let π : pushout φ₁ φ₂ ⟶ Y := pushout.desc (G₁.hom ≫ f₁) (G₂.hom ≫ f₂) (by
    rw [h₁.w_assoc, h₂.w_assoc, hq.w])
  have p1 : pushout.inl φ₁ φ₂ ≫ π = G₁.hom ≫ f₁ := pushout.inl_desc _ _ _
  have p2 : pushout.inr φ₁ φ₂ ≫ π = G₂.hom ≫ f₂ := pushout.inr_desc _ _ _
  have e1 (x : G₁.left) : π (pushout.inl φ₁ φ₂ x) = f₁ (G₁.hom x) := congrArg (fun g => g x) p1
  have e2 (x : G₂.left) : π (pushout.inr φ₁ φ₂ x) = f₂ (G₂.hom x) := congrArg (fun g => g x) p2
  have e3 (w : G₀.left) : pushout.inl φ₁ φ₂ (φ₁ w) = pushout.inr φ₁ φ₂ (φ₂ w) :=
    congrArg (fun g => g w) (pushout.condition (f := φ₁) (g := φ₂))
  refine ⟨Over.mk π, pushout.inl φ₁ φ₂, pushout.inr φ₁ φ₂, (IsOpenImmersion.isPullback _ _ _ _ p1 ?_).flip,
    (IsOpenImmersion.isPullback _ _ _ _ p2 ?_).flip, pushout.condition⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback hq y (G₂.hom x) (hy.trans (e2 x))
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₂ x w hw.symm
        exact ⟨φ₁ z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨G₁.hom y, (e1 y).symm⟩
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hq (G₁.hom x) y (hy.trans (e1 x)).symm
        obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₁ x w hw.symm
        exact ⟨φ₂ z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨G₂.hom y, (e2 y).symm⟩

theorem exists_semiAbelian_two {Y Y₀ Y₁ Y₂ : Scheme.{0}} {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [o₁ : IsOpenImmersion f₁]
    [o₂ : IsOpenImmersion f₂] {q₁ : Y₀ ⟶ Y₁} {q₂ : Y₀ ⟶ Y₂} (hq : IsPullback q₁ q₂ f₁ f₂)
    (hcov : ∀ y : Y, y ∈ Set.range f₁ ∨ y ∈ Set.range f₂)
    {G₁ : Over Y₁} [i₁ : GrpObj G₁] {G₂ : Over Y₂} [i₂ : GrpObj G₂] {G₀ : Over Y₀} [GrpObj G₀]
    {φ₁ : G₀.left ⟶ G₁.left} {φ₂ : G₀.left ⟶ G₂.left} (s₁ : IsSemiAbelian G₁) (s₂ : IsSemiAbelian G₂)
    (h₁ : IsGrpPullback G₀ G₁ q₁ φ₁) (h₂ : IsGrpPullback G₀ G₂ q₂ φ₂) :
    ∃ (G : Over Y) (_ : GrpObj G) (ψ₁ : G₁.left ⟶ G.left) (ψ₂ : G₂.left ⟶ G.left), IsSemiAbelian G ∧
      IsGrpPullback G₁ G f₁ ψ₁ ∧ IsGrpPullback G₂ G f₂ ψ₂ ∧ φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂ := by
  obtain ⟨G, ψ₁, ψ₂, p₁, p₂, hφ⟩ := exists_scheme_two hq h₁.1 h₂.1
  have m₂ : Mono ψ₂ := by
    have : IsOpenImmersion ψ₂ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) p₂.flip inferInstance
    infer_instance
  have base : ∀ {S : Scheme.{0}} {u : S ⟶ Y₁} {v : S ⟶ Y₂} (a : Over.mk u ⟶ G₁) (b : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ w : S ⟶ Y₀, w ≫ q₁ = u ∧ w ≫ q₂ = v := by
    intro S u v a b h
    have e₁ : a.left ≫ G₁.hom = u := Over.w a
    have e₂ : b.left ≫ G₂.hom = v := Over.w b
    have e : u ≫ f₁ = v ≫ f₂ := by
      rw [← e₁, ← e₂, Category.assoc, Category.assoc, ← p₁.w, ← p₂.w, reassoc_of% h]
    exact ⟨hq.lift u v e, hq.lift_fst _ _ _, hq.lift_snd _ _ _⟩
  have common : ∀ {S : Scheme.{0}} (w : S ⟶ Y₀) (a : Over.mk (w ≫ q₁) ⟶ G₁) (b : Over.mk (w ≫ q₂) ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → ∃ c : Over.mk w ⟶ G₀, a.left = c.left ≫ φ₁ ∧ b.left = c.left ≫ φ₂ := by
    intro S w a b h
    refine ⟨Over.homMk (h₁.1.lift a.left w (Over.w a)) (h₁.1.lift_snd _ _ _), (h₁.1.lift_fst _ _ _).symm, ?_⟩
    rw [← cancel_mono ψ₂, ← h, Category.assoc, ← hφ]
    exact (h₁.1.lift_fst_assoc _ _ _ _).symm
  have cm : ∀ {S : Scheme.{0}} {u : S ⟶ Y₁} {v : S ⟶ Y₂} (a a' : Over.mk u ⟶ G₁) (b b' : Over.mk v ⟶ G₂),
      a.left ≫ ψ₁ = b.left ≫ ψ₂ → a'.left ≫ ψ₁ = b'.left ≫ ψ₂ → (a * a').left ≫ ψ₁ = (b * b').left ≫ ψ₂ := by
    intro S u v a a' b b' h h'
    obtain ⟨w, rfl, rfl⟩ := base a b h
    obtain ⟨c, c₁, c₂⟩ := common w a b h
    obtain ⟨c', c₁', c₂'⟩ := common w a' b' h'
    have e₁ : (a * a').left = (c * c').left ≫ φ₁ := h₁.2 _ c c' a a' c₁ c₁'
    have e₂ : (b * b').left = (c * c').left ≫ φ₂ := h₂.2 _ c c' b b' c₂ c₂'
    rw [e₁, e₂, Category.assoc, Category.assoc, hφ]
  let T : Bool → Scheme.{0} := fun i => Bool.rec Y₁ Y₂ i
  let t : ∀ i, T i ⟶ Y := fun i => Bool.rec (motive := fun i => T i ⟶ Y) f₁ f₂ i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by
    cases i
    exacts [o₁, o₂]
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hcov x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  let H : ∀ i : 𝒰.I₀, Over (𝒰.X i) := fun i => Bool.rec (motive := fun i => Over (T i)) G₁ G₂ i
  letI iH : ∀ i : 𝒰.I₀, GrpObj (H i) := fun i => Bool.rec (motive := fun i => GrpObj (H i)) i₁ i₂ i
  let ψ : ∀ i : 𝒰.I₀, (H i).left ⟶ G.left := fun i => Bool.rec (motive := fun i => (H i).left ⟶ G.left) ψ₁ ψ₂ i
  have hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i) := by
    rintro (_ | _)
    exacts [p₁, p₂]
  have same : ∀ (i : 𝒰.I₀) {S : Scheme.{0}} {u v : S ⟶ 𝒰.X i} (a : Over.mk u ⟶ H i) (b : Over.mk v ⟶ H i),
      a.left ≫ ψ i = b.left ≫ ψ i → u = v := fun i S u v a b h => by
    rw [← cancel_mono (𝒰.f i), base_eq hψ a, base_eq hψ b, h]
  have hm : MulCompat ψ := by
    have d : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (u v : S ⟶ 𝒰.X i) (a a' : Over.mk u ⟶ H i) (b b' : Over.mk v ⟶ H i),
        a.left ≫ ψ i = b.left ≫ ψ i → a'.left ≫ ψ i = b'.left ≫ ψ i →
          (a * a').left ≫ ψ i = (b * b').left ≫ ψ i := by
      intro i S u v a a' b b' h h'
      obtain rfl := same i a b h
      rw [pt_ext hψ h, pt_ext hψ h']
    rintro (_ | _) (_ | _) S u v a a' b b' h h'
    · exact d _ S u v a a' b b' h h'
    · exact cm a a' b b' h h'
    · exact (cm b b' a a' h.symm h'.symm).symm
    · exact d _ S u v a a' b b' h h'
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  exact ⟨G, iG, ψ₁, ψ₂, isSemiAbelian_of_charts hG (by rintro (_ | _); exacts [s₁, s₂]), hG false, hG true, hφ⟩

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {k : S'' ⟶ S} (w : g ≫ f = k) {F : G''.left ⟶ G.left}
    (h : IsGrpPullback G'' G k F) : ∃ e, IsGrpPullback G'' ((Over.pullback f).obj G) g e := by
  subst w
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor f g h⟩

theorem isDominant_of_isPullback {X X₁ Y Y₁ : Scheme.{0}} {k : X₁ ⟶ X} {j₁ : X₁ ⟶ Y₁} {j : X ⟶ Y} {f : Y₁ ⟶ Y}
    [IsOpenImmersion f] (hj : IsDominant j) (h : IsPullback k j₁ j f) : IsDominant j₁ := by
  refine ⟨(hj.denseRange.preimage f.isOpenEmbedding.isOpenMap).mono ?_⟩
  rintro y ⟨x, hx⟩
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback h x y hx
  exact ⟨z, hz⟩

theorem isNoetherian_of_isOpenImmersion {Y S : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (f : Y ⟶ S)
    [IsOpenImmersion f] : AlgebraicGeometry.IsNoetherian Y := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion f
  have : TopologicalSpace.NoetherianSpace Y := f.isOpenEmbedding.isInducing.noetherianSpace
  exact {}

theorem hasExt_two {X X₁ Y Y₁ Y₂ : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y₁]
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₁) {f₁ : Y₁ ⟶ Y} {f₂ : Y₂ ⟶ Y} [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] (hcov : ∀ y : Y, y ∈ Set.range f₁ ∨ y ∈ Set.range f₂) {j₂ : X ⟶ Y₂} {k : X₁ ⟶ X}
    {j₁ : X₁ ⟶ Y₁} [IsOpenImmersion j₁] [IsDominant j₁] (w : k ≫ j₂ ≫ f₂ = j₁ ≫ f₁) {A : Over X} [GrpObj A]
    (h₁ : HasExt j₁ ((Over.pullback k).obj A)) (h₂ : HasExt j₂ A) : HasExt (j₂ ≫ f₂) A := by
  obtain ⟨G₁, i₁, e₁, s₁, g₁⟩ := h₁
  obtain ⟨G₂, i₂, e₂, s₂, g₂⟩ := h₂
  let j₀ : X₁ ⟶ pullback f₁ f₂ := pullback.lift j₁ (k ≫ j₂) (by rw [Category.assoc, w])
  have w₁ : j₀ ≫ pullback.fst f₁ f₂ = j₁ := pullback.lift_fst _ _ _
  have w₂ : j₀ ≫ pullback.snd f₁ f₂ = k ≫ j₂ := pullback.lift_snd _ _ _
  have : IsOpenImmersion (j₀ ≫ pullback.fst f₁ f₂) := by rw [w₁]; infer_instance
  have : IsOpenImmersion j₀ := IsOpenImmersion.of_comp j₀ (pullback.fst f₁ f₂)
  have : IsDominant (j₀ ≫ pullback.fst f₁ f₂) := by rw [w₁]; infer_instance
  have : IsDominant j₀ := IsDominant.of_comp_of_isOpenImmersion j₀ (pullback.fst f₁ f₂)
  have := isNoetherian_of_isOpenImmersion (pullback.fst f₁ f₂)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have hn₀ := GlobalTheory.IsNormalScheme.of_isOpenImmersion (pullback.fst f₁ f₂)
  obtain ⟨a₁, ha₁⟩ := exists_factor _ _ w₁ g₁
  obtain ⟨a₂, ha₂⟩ := exists_factor _ _ w₂ ((isGrpPullback_pullback A k).comp g₂)
  obtain ⟨E, ⟨hE, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsSemiAbelian.pullback _ G₁ s₁) (IsSemiAbelian.pullback _ G₂ s₂) ha₁ ha₂
  obtain ⟨G, iG, ψ₁, ψ₂, s, -, g, -⟩ := exists_semiAbelian_two (IsPullback.of_hasPullback f₁ f₂) hcov s₁ s₂
    (isGrpPullback_pullback G₁ _)
    (((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso E).comp (isGrpPullback_pullback G₂ _)).congr
      (Category.id_comp _) rfl)
  exact ⟨G, iG, e₂ ≫ ψ₂, s, g₂.comp g⟩

theorem hasExt_of_locally : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A)) → HasExt j A := by
  intro X S _ hn j _ hj A _ hA hloc
  classical
  choose U hU hE using hloc
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have key : ∀ t : Finset S, ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (_ : IsOpenImmersion f) (i : X ⟶ Y), i ≫ f = j ∧
      HasExt i A ∧ ∀ s ∈ t, (U s : Set S) ⊆ Set.range f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨X, j, inferInstance, 𝟙 X, Category.id_comp _, ⟨A, inferInstance, _, isSemiAbelian_of_isAbelianScheme A hA,
        @ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso _ A A _ _ (Iso.refl A) (inferInstanceAs (IsMonHom (𝟙 A)))⟩,
        by simp⟩
    | insert s t _ ih =>
      obtain ⟨Y, f, _, i, hi, hext, ht⟩ := ih
      let W : S.Opens := U s ⊔ f.opensRange
      have r₂ : Set.range f ⊆ Set.range W.ι := by
        rw [Scheme.Opens.range_ι]
        exact fun y hy => Or.inr hy
      let f₁ : (U s).toScheme ⟶ W.toScheme := S.homOfLE le_sup_left
      let f₂ : Y ⟶ W.toScheme := IsOpenImmersion.lift W.ι f r₂
      have w₁ : f₁ ≫ W.ι = (U s).ι := Scheme.homOfLE_ι _ _
      have w₂ : f₂ ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
      have : IsOpenImmersion (f₂ ≫ W.ι) := by rw [w₂]; infer_instance
      have : IsOpenImmersion f₂ := IsOpenImmersion.of_comp f₂ W.ι
      have := isNoetherian_of_isOpenImmersion (U s).ι
      have : IsDominant (j ∣_ U s) := isDominant_of_isPullback hj (isPullback_morphismRestrict j (U s)).flip
      refine ⟨W, W.ι, inferInstance, i ≫ f₂, by rw [Category.assoc, w₂, hi], ?_, ?_⟩
      · refine hasExt_two (f₁ := f₁) (GlobalTheory.IsNormalScheme.pred _) ?_ ?_ (hE s) hext
        · rintro ⟨y, hy | ⟨z, hz⟩⟩
          · exact Or.inl ⟨⟨y, hy⟩, W.ι.isOpenEmbedding.injective (congrArg (fun g => g ⟨y, hy⟩) w₁)⟩
          · exact Or.inr ⟨z, W.ι.isOpenEmbedding.injective ((congrArg (fun g => g z) w₂).trans hz)⟩
        · rw [← cancel_mono W.ι]
          simp only [Category.assoc, w₁, w₂, hi, morphismRestrict_ι]
      · intro s' hs'
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · rw [Scheme.Opens.range_ι]
          exact fun y hy => Or.inl hy
        · exact (ht s' hs').trans r₂
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s : S => (U s : Set S)) (fun s => (U s).isOpen)
    (fun s _ => Set.mem_iUnion.2 ⟨s, hU s⟩)
  obtain ⟨Y, f, _, i, hi, ⟨G, iG, e, s, g⟩, hf⟩ := key t
  have : Surjective f := ⟨fun y => by
    obtain ⟨s, hs, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact hf s hs hy⟩
  have : IsIso f := (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨a, ha⟩ := exists_factor (inv f) j (k := i) (by rw [← hi]; simp) g
  exact ⟨_, inferInstance, a, IsSemiAbelian.pullback _ G s, ha⟩

end GlobalTheory.ExtGlue
