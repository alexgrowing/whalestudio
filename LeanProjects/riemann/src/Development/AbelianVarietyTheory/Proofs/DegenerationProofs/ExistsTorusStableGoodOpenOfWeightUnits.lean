import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.TorusSlice

theorem isOpenImmersion_of_flat_cover {W A P G : Scheme.{0}} {q : W ⟶ P} {p : W ⟶ A} {a : P ⟶ G} {m : A ⟶ G}
    (h : IsPullback q p a m) [IsOpenImmersion p] [Flat m] [LocallyOfFinitePresentation m] [QuasiCompact m]
    (hr : Set.range a ⊆ Set.range m) : IsOpenImmersion a := by
  let U : G.Opens := ⟨Set.range m, m.isOpenMap.isOpen_range⟩
  have hU : Set.range U.ι = Set.range m := U.range_ι
  let m' := IsOpenImmersion.lift U.ι m hU.ge
  let a' := IsOpenImmersion.lift U.ι a (hr.trans hU.ge)
  have em : m' ≫ U.ι = m := IsOpenImmersion.lift_fac _ _ _
  have ea : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hm : IsPullback m' (𝟙 _) U.ι m := IsPullback.of_vert_isIso_mono ⟨em.trans (Category.id_comp _).symm⟩
  have hs : Surjective m' := ⟨fun u => by
    obtain ⟨y, hy⟩ := u.2
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, em]; exact hy⟩
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) m' :=
    ⟨⟨hs, MorphismProperty.of_isPullback hm.flip ‹Flat m›⟩, MorphismProperty.of_isPullback hm.flip ‹QuasiCompact m›⟩
  have H : IsPullback q p a' m' := by
    refine ⟨⟨by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ea, em, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => h.lift s.fst s.snd (by rw [← ea, ← em, s.condition_assoc])) (fun s => h.lift_fst _ _ _)
      (fun s => h.lift_snd _ _ _) fun s l h1 h2 => h.hom_ext ?_ ?_⟩⟩
    · rw [h1, h.lift_fst]
    · rw [h2, h.lift_snd]
  have : IsOpenImmersion a' := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip hq ‹_›
  rw [← ea]; infer_instance

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft (T : Over S) {Y G : Over S} (j : Y ⟶ G) :
    IsPullback (T ◁ j) (snd T Y) (snd T G) j := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst _ _) s.snd) (fun s => ?_)
    (fun s => by simp) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h1]
    · simp [h2]

def shearIso {T G : Over S} [GrpObj G] (i : T ⟶ G) : T ⊗ G ≅ T ⊗ G where
  hom := lift (fst T G) ((fst T G ≫ i) * snd T G)
  inv := lift (fst T G) ((fst T G ≫ i)⁻¹ * snd T G)
  hom_inv_id := by ext1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  inv_hom_id := by ext1 <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

def Equivar {T G Y : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) (j : Y ⟶ G) (σ : Y ⟶ T) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ T) (y y' : Z ⟶ Y), y' ≫ j = (t ≫ i) * (y ≫ j) → y' ≫ σ = t * (y ≫ σ)

theorem isPullback_sweep {T G Y Y₁ W : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) [IsMonHom i] (j : Y ⟶ G) [Mono j]
    (σ : Y ⟶ T) (hσ : Equivar i j σ) (e : Y₁ ⟶ Y) (he : IsPullback e (toUnit Y₁) σ η[T])
    (p : W ⟶ T ⊗ Y) (r : W ⟶ Y) (hW : IsPullback p r (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) j) :
    ∃ q, IsPullback q p ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) ((fst T Y ≫ i) * (snd T Y ≫ j)) := by
  have he1 : e ≫ σ = 1 := he.w
  have hpr : r ≫ j = ((p ≫ snd T Y ≫ σ)⁻¹ ≫ i) * ((p ≫ snd T Y) ≫ j) := by
    rw [← hW.w]
    simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
  have hr : r ≫ σ = 1 := by
    rw [hσ _ _ _ _ hpr, Category.assoc, inv_mul_cancel]
  obtain ⟨r', er, -⟩ := he.exists_lift r (toUnit _) hr
  have key : ∀ {Z : Over S} (u : Z ⟶ T ⊗ Y₁) (v : Z ⟶ T ⊗ Y),
      u ≫ ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) = v ≫ ((fst T Y ≫ i) * (snd T Y ≫ j)) →
      u ≫ fst T Y₁ = (v ≫ fst T Y) * (v ≫ snd T Y ≫ σ) ∧
        v ≫ (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) = (u ≫ snd T Y₁ ≫ e) ≫ j := by
    intro Z u v h
    have h1 : (v ≫ snd T Y) ≫ j = (((v ≫ fst T Y)⁻¹ * (u ≫ fst T Y₁)) ≫ i) * ((u ≫ snd T Y₁ ≫ e) ≫ j) := by
      simp only [MonObj.comp_mul] at h
      rw [MonObj.mul_comp, GrpObj.inv_comp, _root_.mul_assoc, eq_inv_mul_iff_mul_eq]
      simpa using h.symm
    have h2 := hσ _ _ _ _ h1
    simp only [Category.assoc, he1, MonObj.comp_one, _root_.mul_one] at h2
    refine ⟨by rw [h2, mul_inv_cancel_left], ?_⟩
    simp only [MonObj.comp_mul]
    rw [← Category.assoc v (snd T Y) j, h1, ← h2, ← Category.assoc v, GrpObj.comp_inv, GrpObj.inv_comp,
      inv_mul_cancel_left]
  have hp : Mono p := ⟨fun a b h => hW.hom_ext h (by rw [← cancel_mono j, Category.assoc, Category.assoc, ← hW.w, reassoc_of% h])⟩
  refine ⟨lift ((p ≫ fst T Y) * (p ≫ snd T Y ≫ σ)) r', ⟨?_⟩,
    ⟨PullbackCone.IsLimit.mk _ (fun s => hW.lift s.snd _ (key _ _ s.condition).2) (fun s => ?_)
      (fun s => hW.lift_fst _ _ _) fun s l h1 h2 => ?_⟩⟩
  · simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, reassoc_of% er, hpr, MonObj.mul_comp,
      GrpObj.inv_comp]
    simp [_root_.mul_assoc]
  · ext1
    · simp [MonObj.comp_mul, (key _ _ s.condition).1]
    · refine he.hom_ext ?_ (toUnit_unique _ _)
      simp [er]
  · rw [← cancel_mono p, h2]
    exact (hW.lift_fst _ _ _).symm

theorem isOpenImmersion_sweep {T G Y Y₁ : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) [IsMonHom i] (j : Y ⟶ G)
    (σ : Y ⟶ T) (hσ : Equivar i j σ) (e : Y₁ ⟶ Y) (he : IsPullback e (toUnit Y₁) σ η[T])
    [Flat T.hom] [LocallyOfFinitePresentation T.hom] [QuasiCompact T.hom] [IsOpenImmersion j.left] [QuasiCompact j.left] :
    IsOpenImmersion ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)).left := by
  have hj : Mono j := Over.mono_of_mono_left j
  let m : T ⊗ Y ⟶ G := (fst T Y ≫ i) * (snd T Y ≫ j)
  have em : m.left = (T ◁ j).left ≫ (shearIso i).hom.left ≫ (snd T G).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [m, shearIso, MonObj.comp_mul]
  have hw := (isPullback_whiskerLeft T j).map (Over.forget S)
  have : IsOpenImmersion (T ◁ j).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hw.flip ‹_›
  have : QuasiCompact (T ◁ j).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hw.flip ‹_›
  have : IsIso (shearIso i).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (shearIso i).hom))
  have : Flat (snd T G).left := inferInstanceAs (Flat (pullback.snd T.hom G.hom))
  have : QuasiCompact (snd T G).left := inferInstanceAs (QuasiCompact (pullback.snd T.hom G.hom))
  have : LocallyOfFinitePresentation (snd T G).left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd T.hom G.hom))
  have : Flat m.left := by rw [em]; infer_instance
  have : QuasiCompact m.left := by rw [em]; infer_instance
  have : LocallyOfFinitePresentation m.left := by rw [em]; infer_instance
  have hW := IsPullback.of_hasPullback (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) j
  obtain ⟨q, H⟩ := isPullback_sweep i j σ hσ e he _ _ hW
  have hp := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hW.map (Over.forget S)).flip ‹_›
  refine @isOpenImmersion_of_flat_cover _ _ _ _ _ _ _ m.left (H.map (Over.forget S)) hp _ _ _ ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨(T ◁ e).left x, ?_⟩
  have : T ◁ e ≫ m = (fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j) := by simp [m, MonObj.comp_mul]
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, this]

variable {X : Type} [AddCommGroup X]

def ch {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : Γ(Z.left, ⊤) := t.left.appTop.hom (charUnit S X χ).val

theorem ch_eq {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) :
    ch t χ = (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val := (splitTorusPointsEquiv_val S X Z t χ).symm

theorem ch_mul {Z : Over S} (t t' : Z ⟶ splitTorus S X) (χ : X) : ch (t * t') χ = ch t χ * ch t' χ := by
  simp only [ch_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]

theorem ch_comp {Z Y : Over S} (y : Z ⟶ Y) (t : Y ⟶ splitTorus S X) (χ : X) :
    ch (y ≫ t) χ = y.left.appTop.hom (ch t χ) := by
  simp only [ch, Over.comp_left, Scheme.Hom.comp_appTop]; rfl

theorem ext_basis {I : Type} (b : Module.Basis I ℤ X) {Z : Over S} {t t' : Z ⟶ splitTorus S X}
    (h : ∀ n, ch t (b n) = ch t' (b n)) : t = t' := by
  apply (splitTorusPointsEquiv S X Z).injective
  apply MonoidHom.toAdditiveRight.injective
  apply AddMonoidHom.toIntLinearMap_injective
  refine b.ext fun n => ?_
  have := h n
  rw [ch_eq, ch_eq] at this
  exact congrArg Additive.ofMul (Units.ext this)

theorem exists_of_basis {I : Type} (b : Module.Basis I ℤ X) {Z : Over S} (v : I → Γ(Z.left, ⊤)ˣ) :
    ∃ t : Z ⟶ splitTorus S X, ∀ n, ch t (b n) = (v n).val := by
  refine ⟨(splitTorusPointsEquiv S X Z).symm (MonoidHom.toAdditiveRight.symm
    (b.constr ℤ fun n => Additive.ofMul (v n)).toAddMonoidHom), fun n => ?_⟩
  rw [ch_eq, MulEquiv.apply_symm_apply]
  exact congrArg (fun x : Additive Γ(Z.left, ⊤)ˣ => x.toMul.val) (b.constr_basis ℤ (fun n => Additive.ofMul (v n)) n)

theorem appLE_comp_top {Z Y G : Over S} (y : Z ⟶ Y) (f : Y ⟶ G) (g : Z ⟶ G) (e : g = y ≫ f) (U : G.left.Opens)
    (h : ⊤ ≤ g.left ⁻¹ᵁ U) (h' : ⊤ ≤ f.left ⁻¹ᵁ U) (u : Γ(G.left, U)) :
    (g.left.appLE U ⊤ h).hom u = y.left.appTop.hom ((f.left.appLE U ⊤ h').hom u) := by
  subst e
  have := Scheme.Hom.appLE_comp_appLE y.left f.left U ⊤ ⊤ h' le_top
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact (congrArg (fun φ => φ.hom u) this).symm

theorem goodOpen_of_equivar {G P : Over S} [GrpObj G] (i : splitTorus S X ⟶ G) (a : P ⟶ G) [IsOpenImmersion a.left]
    [IsAffine P.left] (τ : P ⟶ splitTorus S X) (hτ : Equivar i a τ)
    (hs : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (p : Z ⟶ P), ∃ p' : Z ⟶ P, p' ≫ a = (t ≫ i) * (p ≫ a)) :
    GoodOpen i (a.left ''ᵁ ⊤) := by
  have hV : ∀ x, x ∈ a.left ''ᵁ ⊤ ↔ x ∈ Set.range a.left := fun x => by
    rw [Scheme.Hom.image_top_eq_opensRange]; rfl
  have hm : Mono a := Over.mono_of_mono_left a
  refine ⟨(isAffineOpen_top _).image_of_isOpenImmersion _, fun z hz => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := (hV _).1 hz
    obtain ⟨w, rfl, -⟩ := Scheme.exists_preimage_of_isPullback
      ((isPullback_whiskerLeft (splitTorus S X) a).map (Over.forget S)) z y hy.symm
    obtain ⟨p', hp'⟩ := hs _ (fst (splitTorus S X) P) (snd _ _)
    refine (hV _).2 ⟨p'.left w, ?_⟩
    have : p' ≫ a = (splitTorus S X ◁ a) ≫ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G) := by
      simp [hp', MonObj.comp_mul]
    exact congrArg (fun f : splitTorus S X ⊗ P ⟶ G => f.left w) this
  · have h0 : ⊤ ≤ a.left ⁻¹ᵁ (a.left ''ᵁ ⊤) := (a.left.preimage_image_eq ⊤).ge
    have hψ : ∀ x, (a.left.appLE _ ⊤ h0).hom ((a.left.appIso ⊤).inv.hom x) = x := fun x => by
      rw [← Scheme.Hom.appIso_hom']
      exact congrArg (fun φ => φ.hom x) (a.left.appIso ⊤).inv_hom_id
    have lift : ∀ {Z : Over S} (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ (a.left ''ᵁ ⊤) → ∃ p : Z ⟶ P, g = p ≫ a := by
      intro Z g h
      have hr : Set.range g.left ⊆ Set.range a.left := by
        rintro _ ⟨z, rfl⟩
        exact (hV _).1 (h (Set.mem_univ z))
      refine ⟨Over.homMk (IsOpenImmersion.lift a.left g.left hr) ?_, ?_⟩
      · rw [← Over.w a, IsOpenImmersion.lift_fac_assoc, Over.w]
      · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hr).symm
    refine ⟨(Units.map (a.left.appIso ⊤).inv.hom.toMonoidHom).comp (splitTorusPointsEquiv S X P τ),
      fun χ Z t g h₁ h₂ => ?_⟩
    obtain ⟨p, hp⟩ := lift g h₂
    obtain ⟨p', hp'⟩ := lift _ h₁
    rw [appLE_comp_top p' a _ hp' _ h₁ h0, appLE_comp_top p a _ hp _ h₂ h0]
    have e : (a.left.appLE _ ⊤ h0).hom (((Units.map (a.left.appIso ⊤).inv.hom.toMonoidHom).comp
        (splitTorusPointsEquiv S X P τ)) (Multiplicative.ofAdd χ)).val = ch τ χ := by
      rw [ch_eq]; exact hψ _
    rw [e, ← ch_comp, ← ch_comp, hτ Z t p p' (by rw [← hp', hp]), ch_mul]
    rfl

theorem exists_goodOpen [IsAffine S] [Module.Finite ℤ X] {G Y : Over S} [GrpObj G] [QuasiSeparated G.hom]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (j : Y ⟶ G) [IsOpenImmersion j.left] [IsAffine Y.left]
    (σ₀ : Y ⟶ splitTorus S X) (h₀ : Equivar i j σ₀) (y : 𝟙_ (Over S) ⟶ Y) :
    ∃ V, GoodOpen i V ∧ ∀ s, (y ≫ j).left s ∈ V := by
  let T := splitTorus S X
  let σ : Y ⟶ T := σ₀ * (toUnit Y ≫ (y ≫ σ₀)⁻¹)
  have hσ : Equivar i j σ := fun Z t a a' h => by
    simp only [σ, MonObj.comp_mul, h₀ Z t a a' h, _root_.mul_assoc]
    rw [← Category.assoc, ← Category.assoc a, toUnit_unique (a' ≫ toUnit Y) (a ≫ toUnit Y)]
  have hy : y ≫ σ = 1 := by
    simp only [σ, MonObj.comp_mul]
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit Y) (𝟙 _), Category.id_comp, mul_inv_cancel]
  let Y₁ := pullback σ η[T]
  let e : Y₁ ⟶ Y := pullback.fst _ _
  have he : IsPullback e (toUnit Y₁) σ η[T] := by
    rw [toUnit_unique (toUnit Y₁) (pullback.snd σ η[T])]
    exact IsPullback.of_hasPullback _ _
  have he1 : e ≫ σ = 1 := he.w
  have : IsAffine T.left := isAffine_of_isAffineHom T.hom
  have : IsAffine (𝟙_ (Over S)).left := ‹IsAffine S›
  have : IsAffineHom e.left := MorphismProperty.of_isPullback (P := @IsAffineHom) (he.map (Over.forget S)).flip
    (inferInstanceAs (IsAffineHom (η[T]).left))
  have : IsAffine Y₁.left := isAffine_of_isAffineHom e.left
  have : IsAffineHom (snd T Y₁).left := inferInstanceAs (IsAffineHom (pullback.snd T.hom Y₁.hom))
  have : IsAffine (T ⊗ Y₁).left := isAffine_of_isAffineHom (snd T Y₁).left
  have : QuasiCompact (j.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp _ G.hom
  have := isOpenImmersion_sweep i j σ hσ e he
  refine ⟨_, goodOpen_of_equivar i ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) (fst T Y₁) (fun Z t p p' h => ?_)
    (fun Z t p => ⟨lift (t * (p ≫ fst _ _)) (p ≫ snd _ _), ?_⟩), fun s => ?_⟩
  · have h1 : (p' ≫ snd T Y₁ ≫ e) ≫ j =
        (((p' ≫ fst T Y₁)⁻¹ * (t * (p ≫ fst T Y₁))) ≫ i) * ((p ≫ snd T Y₁ ≫ e) ≫ j) := by
      simp only [MonObj.comp_mul] at h
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, _root_.mul_assoc, eq_inv_mul_iff_mul_eq, _root_.mul_assoc]
      simpa using h
    have h2 := hσ _ _ _ _ h1
    simp only [Category.assoc, he1, MonObj.comp_one, _root_.mul_one] at h2
    exact (eq_inv_mul_iff_mul_eq.1 h2 ▸ (_root_.mul_one _).symm)
  · simp [MonObj.comp_mul, MonObj.mul_comp, _root_.mul_assoc]
  · obtain ⟨y₁, hy₁, -⟩ := he.exists_lift y (toUnit _) hy
    have : y ≫ j = lift 1 y₁ ≫ ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) := by
      simp [MonObj.comp_mul, reassoc_of% hy₁]
    rw [this, Scheme.Hom.image_top_eq_opensRange, Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem exists_point {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [LocallyOfFiniteType G.hom]
    {Z : Set G.left} (hZ : Z.Nonempty) (h : IsLocallyClosed Z) :
    ∃ p : 𝟙_ (Over (Sp k)) ⟶ G, ∀ s, p.left s ∈ Z := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  obtain ⟨x, hx, hc⟩ := nonempty_inter_closedPoints hZ h
  exact ⟨Over.homMk (pointOfClosedPoint (K := k) G.hom x hc) (pointOfClosedPoint_comp (K := k) G.hom x hc),
    fun s => (pointOfClosedPoint_apply (K := k) G.hom x hc s).symm ▸ hx⟩

end GlobalTheory.SS.TorusSlice

namespace GlobalTheory.SS
open TorusSlice

theorem exists_goodOpen_of_weight_units : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ χ : X, ∃ (U : G.left.Opens) (u : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit u ∧ Wt i U u χ) → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) := by
  intro k _ _ G _ hG X _ _ _ i hi H x
  obtain ⟨-, hsm, hsep, -, -⟩ := hG
  let b := Module.Free.chooseBasis ℤ X
  choose U u hne hu hw using H
  obtain ⟨p, hp⟩ := exists_point G (Z := closure {x}) ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  choose y hy using fun χ => exists_point G (hne χ) (U χ).isOpen.isLocallyClosed
  let ρ : X → (G ⟶ G) := fun χ => 𝟙 G * (toUnit G ≫ (p⁻¹ * y χ))
  have hρ : ∀ χ, p ≫ ρ χ = y χ := fun χ => by
    simp only [ρ, MonObj.comp_mul]
    rw [← Category.assoc, ← Category.assoc, toUnit_unique (p ≫ toUnit G) (𝟙 _)]
    simp
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let O : G.left.Opens := ⟨⋂ n, ((ρ (b n)).left ⁻¹ᵁ U (b n) : G.left.Opens),
    isOpen_iInter_of_finite fun n => TopologicalSpace.Opens.isOpen _⟩
  have hO : p.left pt ∈ O := Set.mem_iInter.2 fun n => by
    change (ρ (b n)).left (p.left pt) ∈ U (b n)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hρ]
    exact hy _ _
  obtain ⟨Y₀, hY₀, hpY, hYO⟩ := exists_isAffineOpen_mem_and_subset hO
  let Y : Over (Sp k) := Over.mk (Y₀.ι ≫ G.hom)
  let j : Y ⟶ G := Over.homMk Y₀.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion Y₀.ι)
  have : IsAffine Y.left := hY₀
  have hr : Set.range p.left ⊆ Set.range Y₀.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) s pt]
    exact hpY
  let y₀ : 𝟙_ (Over (Sp k)) ⟶ Y := Over.homMk (IsOpenImmersion.lift Y₀.ι p.left hr)
    ((IsOpenImmersion.lift_fac_assoc _ _ hr _).trans (Over.w p))
  have hy₀ : y₀ ≫ j = p := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hr)
  have hle : ∀ n, ⊤ ≤ (j ≫ ρ (b n)).left ⁻¹ᵁ U (b n) := fun n z _ => by
    change (j ≫ ρ (b n)).left z ∈ U (b n)
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact Set.mem_iInter.1 (hYO z.2) n
  obtain ⟨σ, hσ⟩ := exists_of_basis (Z := Y) b fun n =>
    ((hu (b n)).map ((j ≫ ρ (b n)).left.appLE (U (b n)) ⊤ (hle n)).hom).unit
  have hE : Equivar i j σ := fun Z t a a' h => ext_basis b fun n => by
    have pre : ∀ c : Z ⟶ Y, ⊤ ≤ (c ≫ j ≫ ρ (b n)).left ⁻¹ᵁ U (b n) := fun c z _ => by
      change (c ≫ j ≫ ρ (b n)).left z ∈ U (b n)
      rw [Over.comp_left, Scheme.Hom.comp_apply]
      exact hle n (Set.mem_univ _)
    have e : (t ≫ i) * (a ≫ j ≫ ρ (b n)) = a' ≫ j ≫ ρ (b n) := by
      rw [← Category.assoc, ← Category.assoc a']
      simp only [ρ, MonObj.comp_mul (a ≫ j), MonObj.comp_mul (a' ≫ j), Category.comp_id]
      rw [← _root_.mul_assoc, ← h, ← Category.assoc, ← Category.assoc,
        toUnit_unique ((a ≫ j) ≫ toUnit G) ((a' ≫ j) ≫ toUnit G)]
    have := hw (b n) Z t (a ≫ j ≫ ρ (b n)) (e ▸ pre a') (pre a)
    rw [appLE_comp_top a' _ _ e _ _ (hle n), appLE_comp_top a _ _ rfl _ _ (hle n)] at this
    rw [ch_mul, ch_comp, ch_comp, hσ, IsUnit.unit_spec]
    exact this
  obtain ⟨V, hV, hpV⟩ := exists_goodOpen i j σ hE y₀
  rw [hy₀] at hpV
  obtain ⟨z, hz, rfl⟩ := mem_closure_iff.1 (hp pt) V V.isOpen (hpV pt)
  exact ⟨V, hz, hV⟩

end GlobalTheory.SS
end
