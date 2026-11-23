import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothModelsIsoOverFgSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToFgSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteTypeModelOfSmoothAffineStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.SpreadGroup

open GlobalTheory.Spread GlobalTheory.GlueModels

def HasModel {V : Type} [CommRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀),
    Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsSeparated p₀ ∧ QuasiCompact p₀ ∧ IsPullback φ p p₀ (spMap f)

structure PairModel {S S₀ U T : Scheme.{0}} (f : S ⟶ S₀) (p : U ⟶ S) (a : T ⟶ U) where

  U₀ : Scheme.{0}

  T₀ : Scheme.{0}

  p₀ : U₀ ⟶ S₀

  a₀ : T₀ ⟶ U₀

  φ : U ⟶ U₀

  τ : T ⟶ T₀
  smooth : Smooth p₀
  sep : IsSeparated p₀
  qc : QuasiCompact p₀
  opn : IsOpenImmersion a₀
  qca : QuasiCompact a₀
  hφ : IsPullback φ p p₀ f
  hτ : IsPullback τ a a₀ φ

attribute [instance] PairModel.smooth PairModel.sep PairModel.qc PairModel.opn PairModel.qca

variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}

def PairModel.refl (p : U ⟶ S) (a : T ⟶ U) [Smooth p] [IsSeparated p] [QuasiCompact p] [IsOpenImmersion a]
    [QuasiCompact a] : PairModel (𝟙 S) p a :=
  ⟨U, T, p, a, 𝟙 _, 𝟙 _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, .of_horiz_isIso ⟨by simp⟩, .of_horiz_isIso ⟨by simp⟩⟩

theorem isPullback_lift {X X₀ : Scheme.{0}} {q : X ⟶ S} {q₀ : X₀ ⟶ S₀} {φ : X ⟶ X₀} (h : IsPullback φ q q₀ f)
    (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    IsPullback (pullback.lift φ (q ≫ σ) (by rw [Category.assoc, e, h.w])) q (pullback.snd q₀ g) σ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q₀ g) (v₁₃ := q₀) (h₂₂ := g) ?_ (pullback.lift_snd _ _ _)
    (.of_hasPullback _ _)
  rw [pullback.lift_fst, e]
  exact h

def PairModel.baseChange (M : PairModel f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) : PairModel σ p a :=
  have w : M.τ ≫ M.a₀ ≫ M.p₀ = ((a ≫ p) ≫ σ) ≫ g := by
    rw [M.hτ.w_assoc, M.hφ.w, Category.assoc, Category.assoc, e]
  let a₁ : pullback (M.a₀ ≫ M.p₀) g ⟶ pullback M.p₀ g :=
    pullback.lift (pullback.fst _ _ ≫ M.a₀) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have h₁ : IsPullback (pullback.fst _ _) a₁ M.a₀ (pullback.fst _ _) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (.of_hasPullback M.p₀ g)
    rw [pullback.lift_snd]
    exact .of_hasPullback _ _
  { U₀ := pullback M.p₀ g
    T₀ := pullback (M.a₀ ≫ M.p₀) g
    p₀ := pullback.snd _ _
    a₀ := a₁
    φ := pullback.lift M.φ (p ≫ σ) (by rw [Category.assoc, e, M.hφ.w])
    τ := pullback.lift M.τ ((a ≫ p) ≫ σ) w
    smooth := inferInstance
    sep := inferInstance
    qc := inferInstance
    opn := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁ M.opn
    qca := MorphismProperty.of_isPullback (P := @QuasiCompact) h₁ M.qca
    hφ := isPullback_lift M.hφ σ g e
    hτ := by
      refine IsPullback.of_right ?_ ?_ h₁
      · rw [pullback.lift_fst, pullback.lift_fst]
        exact M.hτ
      · apply pullback.hom_ext
        · simp only [a₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, M.hτ.w]
        · simp only [a₁, Category.assoc, pullback.lift_snd] }

theorem PairModel.baseChange_a₀_p₀ (M : PairModel f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    (M.baseChange σ g e).a₀ ≫ (M.baseChange σ g e).p₀ = pullback.snd (M.a₀ ≫ M.p₀) g :=
  pullback.lift_snd _ _ _

theorem smooth_of_two {X W : Scheme.{0}} {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (q : X ⟶ S) (hu : Smooth (u ≫ q)) (hv : Smooth (v ≫ q)) :
    Smooth q := by
  let Y : Bool → Scheme.{0} := fun i => Bool.rec U W i
  let t : ∀ i, Y i ⟶ X := fun i => Bool.rec (motive := fun i => Y i ⟶ X) u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool Y t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := @RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) 𝒰 ?_
  rintro (_ | _)
  · exact hu
  · exact hv

theorem exists_glued {X W : Scheme.{0}} (q : X ⟶ S) {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    {b : T ⟶ W} (h : IsPullback a b u v) (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    (M : PairModel f (u ≫ q) a) (N : PairModel f (v ≫ q) b) (e : M.T₀ ≅ N.T₀) (he : M.τ ≫ e.hom = N.τ)
    (he' : e.hom ≫ N.a₀ ≫ N.p₀ = M.a₀ ≫ M.p₀) [CompactSpace S₀] [QuasiSeparatedSpace S₀] :
    ∃ (X₀ : Scheme.{0}) (q₀ : X₀ ⟶ S₀) (φ : X ⟶ X₀), Smooth q₀ ∧ QuasiCompact q₀ ∧ IsPullback φ q q₀ f := by
  have Hp := M.hτ
  have Hq : IsPullback M.τ b (e.hom ≫ N.a₀) N.φ :=
    N.hτ.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp [← he]) (by simp) (by simp) (by simp)
  have := isOpenImmersion_inl M.a₀ (e.hom ≫ N.a₀)
  have := isOpenImmersion_inr M.a₀ (e.hom ≫ N.a₀)
  obtain ⟨φ, h1, h2⟩ := exists_glue h hc (M.φ ≫ pushout.inl M.a₀ (e.hom ≫ N.a₀))
    (N.φ ≫ pushout.inr M.a₀ (e.hom ≫ N.a₀)) (by
    rw [← Hp.w_assoc, ← Hq.w_assoc, pushout.condition])
  have e1 (x : U) : φ (u x) = pushout.inl M.a₀ (e.hom ≫ N.a₀) (M.φ x) := congrArg (fun g => g x) h1
  have e2 (x : W) : φ (v x) = pushout.inr M.a₀ (e.hom ≫ N.a₀) (N.φ x) := congrArg (fun g => g x) h2
  have e3 (w : T) : u (a w) = v (b w) := congrArg (fun g => g w) h.w
  have hcov := pushout_cover M.a₀ (e.hom ≫ N.a₀)
  refine ⟨_, pushout.desc M.p₀ N.p₀ (by rw [Category.assoc, he']), φ, ?_, ?_, ?_⟩
  · refine smooth_of_two hcov _ ?_ ?_
    · rw [pushout.inl_desc]
      infer_instance
    · rw [pushout.inr_desc]
      infer_instance
  · have : CompactSpace M.U₀ := QuasiCompact.compactSpace_of_compactSpace M.p₀
    have : CompactSpace N.U₀ := QuasiCompact.compactSpace_of_compactSpace N.p₀
    have : CompactSpace (pushout M.a₀ (e.hom ≫ N.a₀) : Scheme.{0}) := by
      refine ⟨?_⟩
      rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl M.a₀ (e.hom ≫ N.a₀)) ∪
        Set.range (pushout.inr M.a₀ (e.hom ≫ N.a₀))) hcov]
      exact (isCompact_range (Scheme.Hom.continuous _)).union (isCompact_range (Scheme.Hom.continuous _))
    infer_instance
  refine isPullback_of_two hcov (u' := u) (v' := v) (aU := M.φ) (aV := N.φ) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hq w x hw
        exact ⟨a z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨M.φ y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hp w x hw
        exact ⟨b z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨N.φ y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using M.hφ
  · simpa only [pushout.inr_desc] using N.hφ

variable {V : Type} [CommRing V]

theorem finiteType_of_fg {k : Type} [CommRing k] [Algebra k V] (hk : Algebra.FiniteType ℤ k) {R : Subalgebra k V}
    (hR : R.FG) : Algebra.FiniteType ℤ R :=
  Algebra.FiniteType.trans hk ((Subalgebra.fg_iff_finiteType R).1 hR)

theorem exists_pairModel {p : U ⟶ Sp V} (h : HasModel p) (a : T ⟶ U) [IsOpenImmersion a] [CompactSpace T] :
    ∃ (R : Type) (_ : CommRing R) (f : R →+* V), Algebra.FiniteType ℤ R ∧ Nonempty (PairModel (spMap f) p a) := by
  classical
  obtain ⟨k, _, f, X₀, p₀, φ, hk, _, _, _, hφ⟩ := h
  letI := f.toAlgebra
  have hφ' : IsPullback φ p p₀ (spMap (algebraMap k V)) := hφ
  obtain ⟨s, O, hO, hs⟩ := exists_preimage_eq (bcDiagram p₀ V) (bcCone p₀ V) (isLimitBcCone p₀ V)
    (a ≫ hφ'.isoPullback.hom).opensRange (isCompact_range (Scheme.Hom.continuous _))
  let R := Algebra.adjoin k (s.unop : Set V)
  let O' : (pullback p₀ (spMap (algebraMap k R))).Opens := O
  have hs' : bcMap p₀ R.val ⁻¹ᵁ O' = (a ≫ hφ'.isoPullback.hom).opensRange := hs
  have hO' : CompactSpace O' := isCompact_iff_compactSpace.1 hO
  have : QuasiSeparatedSpace ↥(pullback p₀ (spMap (algebraMap k R))) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p₀ _)).mp inferInstance
  have hqc : QuasiCompact O'.ι := quasiCompact_of_compactSpace _
  have hr : (hφ'.isoPullback.hom ≫ bcMap p₀ R.val) ⁻¹ᵁ O'.ι.opensRange = a.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage, hs']
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hφ'.isoPullback.hom.isOpenEmbedding.injective (by simpa using hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
  have hle : Set.range (a ≫ hφ'.isoPullback.hom ≫ bcMap p₀ R.val) ⊆ Set.range O'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hr.ge ⟨y, rfl⟩
  refine ⟨R, inferInstance, R.val.toRingHom, finiteType_of_fg hk (Subalgebra.fg_adjoin_finset _),
    ⟨⟨_, O', pullback.snd p₀ _, O'.ι, hφ'.isoPullback.hom ≫ bcMap p₀ R.val, IsOpenImmersion.lift O'.ι _ hle,
      inferInstance, inferInstance, inferInstance, inferInstance, hqc, ?_, ?_⟩⟩⟩
  · have h₁ : IsPullback hφ'.isoPullback.hom p (pullback.snd _ _) (𝟙 _) := .of_horiz_isIso ⟨by simp⟩
    simpa using h₁.paste_horiz (isPullback_bcMap p₀ R.val)
  · exact IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm hr

theorem exists_common_level {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (f₁ : R₁ →+* V) (f₂ : R₂ →+* V)
    (h₁ : Algebra.FiniteType ℤ R₁) (h₂ : Algebra.FiniteType ℤ R₂) :
    ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (g₁ : R₁ →+* R) (g₂ : R₂ →+* R), Algebra.FiniteType ℤ R ∧
      spMap f ≫ spMap g₁ = spMap f₁ ∧ spMap f ≫ spMap g₂ = spMap f₂ := by
  let R : Subalgebra ℤ V := f₁.toIntAlgHom.range ⊔ f₂.toIntAlgHom.range
  have hR : R.FG := by
    refine Subalgebra.FG.sup ?_ ?_ <;> rw [← Algebra.map_top]
    · exact h₁.out.map _
    · exact h₂.out.map _
  refine ⟨R, inferInstance, R.val.toRingHom,
    f₁.codRestrict R fun x => (le_sup_left : _ ≤ R) ⟨x, rfl⟩,
    f₂.codRestrict R fun x => (le_sup_right : _ ≤ R) ⟨x, rfl⟩, (Subalgebra.fg_iff_finiteType R).1 hR, ?_, ?_⟩ <;>
  · rw [← Spec.map_comp]
    rfl

theorem hasModel_of_two {X W : Scheme.{0}} (q : X ⟶ Sp V) [IsSeparated q] (u : U ⟶ X) (v : W ⟶ X)
    [IsOpenImmersion u] [IsOpenImmersion v] (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    [CompactSpace U] [CompactSpace W] (hU : HasModel (u ≫ q)) (hW : HasModel (v ≫ q)) : HasModel q := by
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace q).mp inferInstance
  have : CompactSpace ↥(pullback u v) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst u v)
  obtain ⟨R₁, _, f₁, h₁, ⟨M₁⟩⟩ := exists_pairModel hU (pullback.fst u v)
  obtain ⟨R₂, _, f₂, h₂, ⟨N₁⟩⟩ := exists_pairModel hW (pullback.snd u v)
  obtain ⟨k, _, f, g₁, g₂, hk, e₁, e₂⟩ := exists_common_level f₁ f₂ h₁ h₂
  letI := f.toAlgebra
  obtain ⟨M⟩ : Nonempty (PairModel (spMap (algebraMap k V)) (u ≫ q) (pullback.fst u v)) := ⟨M₁.baseChange _ _ e₁⟩
  obtain ⟨N⟩ : Nonempty (PairModel (spMap (algebraMap k V)) (v ≫ q) (pullback.snd u v)) := ⟨N₁.baseChange _ _ e₂⟩
  have hN := N.hτ.paste_vert N.hφ
  rw [← pullback.condition_assoc] at hN
  obtain ⟨R, e, hR, he, he'⟩ := GlobalTheory.T.exists_iso_pullback_over_fg_subalgebra k V M.T₀ N.T₀ _ (M.a₀ ≫ M.p₀) (N.a₀ ≫ N.p₀) _ M.τ N.τ
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (M.hτ.paste_vert M.hφ) hN
  have w := spMap_algHom_comp R.val
  obtain ⟨X₀, q₀, φ, _, _, hφ⟩ := exists_glued q (IsPullback.of_hasPullback u v) hc
    (M.baseChange _ _ w) (N.baseChange _ _ w) e (by
      apply pullback.hom_ext
      · refine (Category.assoc _ _ _).trans ?_
        exact (he' _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans (pullback.lift_fst _ _ _).symm
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg _ he).trans ((pullback.lift_snd _ _ _).trans (Eq.trans ?_ (pullback.lift_snd _ _ _).symm))
        simp only [Category.assoc, pullback.condition_assoc])
    (by rw [PairModel.baseChange_a₀_p₀, PairModel.baseChange_a₀_p₀]; exact he)
  have hRZ := finiteType_of_fg hk hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hφ' : IsPullback φ q q₀ (spMap (algebraMap R V)) := hφ
  obtain ⟨R', hR', _⟩ := GlobalTheory.T.exists_fg_subalgebra_isSeparated_pullback_snd R V X₀ q₀ inferInstance inferInstance (by
    rw [← hφ'.isoPullback_inv_snd]; infer_instance)
  exact ⟨R', inferInstance, R'.val.toRingHom, _, pullback.snd q₀ _, _, finiteType_of_fg hRZ hR', inferInstance,
    ‹_›, inferInstance, isPullback_lift hφ' _ _ (spMap_algHom_comp R'.val)⟩

theorem hasModel_of_isAffine {X : Scheme.{0}} (q : X ⟶ Sp V) [IsAffine X] [Smooth q] : HasModel q := by
  obtain ⟨R, _, f, X₀, p₀, φ, h, _, _, hφ⟩ := GlobalTheory.T.exists_finiteType_model_of_smooth_affine' V X q ‹_› ‹_›
  exact ⟨R, _, f, X₀, p₀, φ, h, ‹_›, inferInstance, inferInstance, hφ⟩

theorem hasModel {X : Scheme.{0}} (q : X ⟶ Sp V) [Smooth q] [IsSeparated q] [QuasiCompact q] : HasModel q := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have key : HasModel ((⊤ : X.Opens).ι ≫ q) := by
    refine compact_open_induction_on (P := fun S => HasModel (S.ι ≫ q)) ⊤ isCompact_univ ?_ ?_
    · have : IsAffine (⊥ : X.Opens) := isAffineOpen_bot X
      exact hasModel_of_isAffine _
    · intro S hS W h
      have : CompactSpace S := isCompact_iff_compactSpace.1 hS
      have : IsAffine W.1 := W.2
      refine hasModel_of_two _ (X.homOfLE (le_sup_left : S ≤ S ⊔ W.1)) (X.homOfLE (le_sup_right : W.1 ≤ S ⊔ W.1))
        ?_ ?_ ?_
      · rintro ⟨x, hx | hx⟩
        · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩
        · exact Or.inr ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩
      · rwa [Scheme.homOfLE_ι_assoc]
      · exact hasModel_of_isAffine _
  obtain ⟨R, _, f, X₀, p₀, φ, h₁, h₂, h₃, h₄, hφ⟩ := key
  refine ⟨R, _, f, X₀, p₀, X.topIso.inv ≫ φ, h₁, h₂, h₃, h₄, ?_⟩
  exact hφ.of_iso X.topIso (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end GlobalTheory.SpreadGroup

namespace GlobalTheory

theorem smooth_grpScheme_descends_to_fg_subring : ∀ (V : Type) [CommRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (F : Finset V), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∃ (R : Subring V) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left), (F : Set V) ⊆ R ∧ Algebra.FiniteType ℤ R ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧ QuasiCompact A₀.hom ∧ IsGrpPullback A A₀ (spMap R.subtype) φ := by
  intro V _ A _ _ F h₁ h₂ h₃
  obtain ⟨k, _, f, X₀, p₀, φ, hk, g₁, g₂, g₃, hφ⟩ := SpreadGroup.hasModel A.hom
  letI := f.toAlgebra
  obtain ⟨R, A₀, i₁, i₂, ψ, hF, hR, s₁, s₂, s₃, hψ⟩ := GlobalTheory.T.exists_fg_subalgebra_grpObj_model k V A X₀ p₀ φ F g₁ g₂ g₃ hφ
  exact ⟨R.toSubring, A₀, i₁, i₂, ψ, hF, SpreadGroup.finiteType_of_fg hk hR, s₁, s₂, s₃, hψ⟩

end GlobalTheory
