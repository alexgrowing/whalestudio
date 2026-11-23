import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfieldStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GrpDescent

open GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

def sq (w : φ ≫ G.hom = A.hom ≫ j) : (A ⊗ A).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left

theorem isSquare_sq (w : φ ≫ G.hom = A.hom ≫ j) : IsSquare φ (sq w) := by
  constructor
  · rw [sq, ← Over.comp_left, lift_fst]; rfl
  · rw [sq, ← Over.comp_left, lift_snd]; rfl

theorem sq_ext {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left} (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem eq_sq (w : φ ≫ G.hom = A.hom ≫ j) {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq w :=
  sq_ext (h.1.trans (isSquare_sq w).1.symm) (h.2.trans (isSquare_sq w).2.symm)

theorem isPullback_sq (hA : IsPullback φ A.hom G.hom j) :
    IsPullback (sq hA.w) (A ⊗ A).hom (G ⊗ G).hom j := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := (isSquare_sq hA.w).1
  have h₂ := (isSquare_sq hA.w).2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply sq_ext
    · rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem exists_grpObj (j : U ⟶ Z) [Flat j] [Surjective j] [GrpObj A] (h : IsPullback φ A.hom G.hom j)
    (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G)
    (hm : sq h.w ≫ m.left = (μ[A]).left ≫ φ) (hi : φ ≫ i.left = (ι[A]).left ≫ φ)
    (he : j ≫ e.left = (η[A]).left ≫ φ) : ∃ _ : GrpObj G, IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w (fun φ₂ h₂ => by rw [eq_sq h.w h₂, hm]) (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, h, fun T x y x₀ y₀ hx hy => ?_⟩
  obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
  obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
  exact congrArg (fun z => z.left) (hM x y)

theorem flat_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Flat (spMap β) := by
  rw [Flat.SpecMap_iff]
  letI := β.toAlgebra
  exact (inferInstance : Module.Flat k K)

theorem surjective_spMap {k K : Type} [Field k] [Field K] (β : k →+* K) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

end GlobalTheory.GrpDescent

namespace GlobalTheory

open GrpDescent

theorem grpObj_descends_to_large_subfield :
    ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ := by
  intro K _ K₀ A₀ A _ φ _ _ _ hφ
  have hw := hφ.w
  have hq : QuasiCompact (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiCompact (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  have hs : QuasiSeparated (A₀ ⊗ A₀).hom := by
    rw [← Over.w (fst A₀ A₀)]
    exact (inferInstance : QuasiSeparated (pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨s₁, H₁⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (A₀ ⊗ A₀).hom (A ⊗ A).hom (sq hw) _ A₀.hom Unit
    (fun _ => (μ[A]).left ≫ φ) (isPullback_sq hφ) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w, (isPullback_sq hφ).w])
  obtain ⟨s₂, H₂⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ A₀.hom A.hom φ _ A₀.hom Unit
    (fun _ => (ι[A]).left ≫ φ) hφ (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w])
  obtain ⟨s₃, H₃⟩ := T.exists_descent_of_morphisms_to_subfield K K₀ _ _ (𝟙 _) (𝟙 _) (spMap K₀.subtype) _ A₀.hom Unit
    (fun _ => (η[A]).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩) (fun _ => by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  classical
  refine ⟨s₁ ∪ s₂ ∪ s₃, fun K₁ h hs A₁ φ₁ ψ hφ₁ hψ hψw => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hs
  have hψp : IsPullback ψ A.hom A₁.hom (spMap K₁.subtype) :=
    IsPullback.of_right (by rwa [hψ, spMap_subtype]) hψw hφ₁
  obtain ⟨m, hm⟩ := H₁ K₁ h hs.1.1 _ (A₁ ⊗ A₁).hom (sq hφ₁.w) (sq hψw) (isPullback_sq hφ₁)
    (eq_sq hw ⟨by rw [Category.assoc, (isSquare_sq _).1, reassoc_of% (isSquare_sq hψw).1, hψ],
      by rw [Category.assoc, (isSquare_sq _).2, reassoc_of% (isSquare_sq hψw).2, hψ]⟩) (isPullback_sq hψp).w
  obtain ⟨i, hi⟩ := H₂ K₁ h hs.1.2 _ A₁.hom φ₁ ψ hφ₁ hψ hψw
  obtain ⟨e, he⟩ := H₃ K₁ h hs.2 _ (𝟙 _) (spMap (Subfield.inclusion h)) (spMap K₁.subtype)
    (IsPullback.of_vert_isIso ⟨by simp⟩) (spMap_subtype h) (by simp)
  have := flat_spMap K₁.subtype
  have := surjective_spMap K₁.subtype
  refine exists_grpObj _ hψp
    (Over.homMk (hφ₁.lift (m ()) (A₁ ⊗ A₁).hom ((hm ()).2.trans (isPullback_sq hφ₁).w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (i ()) A₁.hom ((hi ()).2.trans hφ₁.w)) (hφ₁.lift_snd _ _ _))
    (Over.homMk (hφ₁.lift (e ()) (𝟙 _) ((he ()).2.trans (by simp))) (hφ₁.lift_snd _ _ _)) ?_ ?_ ?_
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hm ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [(isPullback_sq hψp).w, ← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (hi ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]
  · apply hφ₁.hom_ext
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst, hψ]
      exact (he ()).1
    · simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd, hψw]
      rw [← Category.assoc, Over.w]; simp

end GlobalTheory
