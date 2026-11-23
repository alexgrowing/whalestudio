import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrpFlatDesc

open GrpDense MorphismProperty

variable {Z U : Scheme.{0}}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst X.hom j)
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

set_option backward.isDefEq.respectTransparency.types false in

theorem isProper_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have h₁ : UniversallyClosed g :=
    of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip hj inferInstance
  have h₂ : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hj inferInstance
  have : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    @IsStableUnderBaseChange.inf _ _ _ _ (@IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance)
      inferInstance
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) @UniversallyClosed := universallyClosed_respectsIso
  have h₃ : UniversallyClosed (pullback.diagonal g) :=
    of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hj
      (show UniversallyClosed (pullback.diagonal f) from inferInstance)
  have h₄ : IsSeparated g :=
    ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩
  exact {}

theorem geometricallyConnected_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [hf : GeometricallyConnected f] : GeometricallyConnected g := by
  refine ⟨fun K _ y W a b hW => ?_⟩

  obtain ⟨p, -⟩ := (pullback.fst y j).surjective (Classical.arbitrary _)
  let r := (Limits.pullback y j).fromSpecResidueField p
  let s := r ≫ pullback.fst y j
  let t := r ≫ pullback.snd y j
  have hst : t ≫ j = s ≫ y := by simp only [t, s, Category.assoc, pullback.condition]
  have hs : Surjective s := inferInstance

  have hc : ConnectedSpace ↥(Limits.pullback f t) := pullback_of_geometrically hf.1 _ t

  have hout : IsPullback (pullback.fst f t ≫ φ) (pullback.snd f t) g (s ≫ y) := by
    rw [← hst]
    exact (IsPullback.of_hasPullback f t).paste_horiz h
  let q : Limits.pullback f t ⟶ W :=
    hW.lift (pullback.fst f t ≫ φ) (pullback.snd f t ≫ s) (by simpa only [Category.assoc] using hout.w)
  have hq : IsPullback q (pullback.snd f t) b s :=
    IsPullback.of_right (by rwa [hW.lift_fst]) (hW.lift_snd _ _ _) hW
  have hqs : Surjective q := MorphismProperty.of_isPullback hq.flip hs
  exact hqs.surj.connectedSpace q.continuous

theorem grpObj_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] (G : Over Z) (A : Over U) [GrpObj A]
    [IsCommMonObj A] (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w hm (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, rfl, rfl, rfl, ⟨GrpFlatDesc.hom_ext_of_points j fun T t => ?_⟩, h, fun T x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.w x) (pushPt h.w y) := by ext <;> simp [hx, hy]
    change _ ≫ _ ≫ m = _ ≫ m
    rw [lift_braiding_hom_assoc, hM, hM, _root_.mul_comm]
  · obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    exact congrArg (fun z => z.left) (hM x y)

theorem isAbelianScheme_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] [QuasiCompact j] (G : Over Z) (A : Over U)
    [GrpObj A] (hA : IsAbelianScheme A) (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G)
    (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G) (φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left) (h₂ : IsSquare φ φ₂)
    (hm : φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, IsAbelianScheme G ∧ IsGrpPullback A G j φ := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, -, -, -, hc, hp⟩ := grpObj_of_flat_cover j G A φ h m i e (fun ψ hψ => by
    obtain rfl : ψ = φ₂ := Over.tensorObj_ext _ _ (hψ.1.trans h₂.1.symm) (hψ.2.trans h₂.2.symm)
    exact hm) hi he
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨inferInstance, ⟨hc, of_isPullback_of_descendsAlong (P := @Smooth) h.flip hj hA.smooth,
    isProper_of_isPullback h, geometricallyConnected_of_isPullback h⟩, hp⟩

end GlobalTheory.GrpFlatDesc

namespace GlobalTheory

theorem isAbelianScheme_descends_subfield :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  intro k K _ _ β B _ B₀ φ hB h m i e φ₂ h₁ h₂ hm hi he
  have : Flat (spMap β) := by
    algebraize [β]
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have : Surjective (spMap β) := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GrpFlatDesc.isAbelianScheme_of_flat_cover (spMap β) B₀ B hB φ h m i e φ₂ ⟨h₁, h₂⟩ hm hi he

end GlobalTheory
