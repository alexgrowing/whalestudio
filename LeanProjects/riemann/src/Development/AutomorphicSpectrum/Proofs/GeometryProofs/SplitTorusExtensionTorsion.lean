import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext

section General
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def pre {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) : (Y ⟶ A) →* (Y' ⟶ A) where
  toFun x := ρ ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

def post {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] : (Y ⟶ A) →* (Y ⟶ A') where
  toFun x := x ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

theorem pre_pow {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) (n : ℕ) : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n :=
  map_pow (pre ρ) x n

theorem post_pow {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n :=
  map_pow (post φ) x n

theorem post_inv {Y A A' : C} [GrpObj A] [GrpObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) :
    x⁻¹ ≫ φ = (x ≫ φ)⁻¹ :=
  map_inv (post φ) x

theorem pre_inv {Y Y' A : C} [GrpObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) : ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  map_inv (pre ρ) x

theorem isPullback_of_lift {Z P G B : C} {f : Z ⟶ P} {g : Z ⟶ G} {h : P ⟶ B} {k : G ⟶ B}
    (w : f ≫ h = g ≫ k) (hm : ∀ {Y : C} {a b : Y ⟶ Z}, a ≫ f = b ≫ f → a ≫ g = b ≫ g → a = b)
    (hl : ∀ {Y : C} (x : Y ⟶ P) (y : Y ⟶ G), x ≫ h = y ≫ k → ∃ l : Y ⟶ Z, l ≫ f = x ∧ l ≫ g = y) :
    IsPullback f g h k :=
  ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst s.snd s.condition).choose)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.1)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.2)
    (fun s m h1 h2 => hm (h1.trans (hl s.fst s.snd s.condition).choose_spec.1.symm)
      (h2.trans (hl s.fst s.snd s.condition).choose_spec.2.symm))⟩⟩

end General

theorem mulN_eq_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih]; rfl

section Main
variable {S : Scheme.{0}} {T Gt B : Over S} [GrpObj T] [IsCommMonObj T] [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B]
  [IsCommMonObj B] {u : T ⟶ Gt} {q : Gt ⟶ B} [IsMonHom u] [IsMonHom q] {N : ℕ}
  {TN GN BN : Over S} {jT : TN ⟶ T} {jG : GN ⟶ Gt} {jB : BN ⟶ B} {eB : 𝟙_ _ ⟶ BN}

theorem mono_of_ext (hu : IsPullback u (toUnit _) q η[B]) : Mono u :=
  ⟨fun _ _ h => hu.hom_ext h (toUnit_unique _ _)⟩

theorem lift_of_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (y : Y ⟶ Gt) (hy : y ≫ q = 1) :
    ∃ z : Y ⟶ T, z ≫ u = y :=
  ⟨hu.lift y (toUnit Y) (by rw [hy, Hom.one_def]), hu.lift_fst _ _ _⟩

theorem comp_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (z : Y ⟶ T) : (z ≫ u) ≫ q = 1 := by
  rw [Category.assoc, hu.w, Hom.one_def, ← Category.assoc, toUnit_unique (z ≫ toUnit T) (toUnit Y)]

theorem isPullback_kernel (hu : IsPullback u (toUnit _) q η[B])
    (hT : IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[T]) (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt])
    (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B]) (he : eB ≫ jB = η[B])
    {a : TN ⟶ GN} {b : GN ⟶ BN} (ha : a ≫ jG = jT ≫ u) (hb : b ≫ jB = jG ≫ q) :
    IsPullback a (toUnit TN) b eB := by
  have := mono_of_ext hu
  have := mono_of_pullback hT
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift S ?_ (fun {Y} x y h => ?_) (fun {Y} t ht => ?_)
  · rw [← cancel_mono jB, Category.assoc, hb, reassoc_of% ha, Category.assoc, he]
    have := comp_ext hu jT
    rw [Category.assoc] at this
    rw [this, Hom.one_def]
  · rw [← cancel_mono jG, Category.assoc, Category.assoc, ha] at h
    rw [← cancel_mono (jT ≫ u)]
    simpa using h
  · have h1 : (t ≫ jG) ≫ q = 1 := by
      have : t ≫ b ≫ jB = t ≫ jG ≫ q := by rw [hb]
      rw [Category.assoc, ← this, ← Category.assoc, ht, Category.assoc, he, Hom.one_def]
    obtain ⟨v, hv⟩ := lift_of_ext hu _ h1
    have h2 : v ^ N = 1 := by
      rw [← cancel_mono u, post_pow, hv, torsion_of_comp hG, MonObj.one_comp]
    obtain ⟨w, hw⟩ := lift_of_torsion hT v h2
    refine ⟨w, ?_⟩
    rw [← cancel_mono jG, Category.assoc, ha, reassoc_of% hw, hv]

theorem exists_isPullback_cover (hu : IsPullback u (toUnit _) q η[B])
    (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt]) (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B])
    {b : GN ⟶ BN} (hb : b ≫ jB = jG ≫ q) {P : Over S} {pG : P ⟶ Gt} {pB : P ⟶ BN} (hP : pG ≫ q = pB ≫ jB) :
    ∃ (φ : P ⟶ T) (c : pullback φ ((𝟙 T) ^ N) ⟶ GN), IsPullback (pullback.fst _ _) c pB b := by
  have := mono_of_ext hu
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  have h0 : (pG ^ N)⁻¹ ≫ q = 1 := by
    rw [post_inv, post_pow, hP, torsion_of_comp hB, inv_one]
  obtain ⟨φ, hφ⟩ := lift_of_ext hu _ h0
  have key : ∀ {Y : Over S} (y : Y ⟶ P), (y ≫ φ) ≫ u = ((y ≫ pG) ^ N)⁻¹ := fun y => by
    rw [Category.assoc, hφ, pre_inv, pre_pow]
  have hz : ∀ {Y : Over S} (z : Y ⟶ T), z ≫ ((𝟙 T) ^ N) = z ^ N := fun z => by
    rw [pre_pow, Category.comp_id]
  have tor : ((pullback.snd φ ((𝟙 T) ^ N) ≫ u) * (pullback.fst φ ((𝟙 T) ^ N) ≫ pG)) ^ N = 1 := by
    rw [mul_pow, ← post_pow u, ← hz (pullback.snd φ ((𝟙 T) ^ N)), ← pullback.condition, key, inv_mul_cancel]
  obtain ⟨c, hc⟩ := lift_of_torsion hG _ tor
  refine ⟨φ, c, isPullback_of_lift ?_ (fun {Y} a a' h1 h2 => ?_) (fun {Y} x k hxk => ?_)⟩
  · rw [← cancel_mono jB, Category.assoc, Category.assoc, hb, ← hP, reassoc_of% hc, MonObj.mul_comp,
      comp_ext hu, _root_.one_mul, Category.assoc]
  · refine pullback.hom_ext h1 ?_
    have h3 : a ≫ c ≫ jG = a' ≫ c ≫ jG := by rw [reassoc_of% h2]
    rw [hc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc a (pullback.fst _ _) pG,
      ← Category.assoc a' (pullback.fst _ _) pG, h1, mul_left_inj] at h3
    rw [← cancel_mono u, Category.assoc, Category.assoc]
    exact h3
  · have e : (k ≫ jG) ≫ q = (x ≫ pG) ≫ q := by
      rw [Category.assoc, Category.assoc, ← hb, hP, reassoc_of% hxk]
    have hw : ((k ≫ jG) * (x ≫ pG)⁻¹) ≫ q = 1 := by
      rw [MonObj.mul_comp, post_inv, e, mul_inv_cancel]
    obtain ⟨s, hs⟩ := lift_of_ext hu _ hw
    have hsN : x ≫ φ = s ≫ ((𝟙 T) ^ N) := by
      rw [← cancel_mono u, key x, hz, post_pow, hs, mul_pow, torsion_of_comp hG, _root_.one_mul, inv_pow]
    refine ⟨pullback.lift x s hsN, pullback.lift_fst _ _ _, ?_⟩
    rw [← cancel_mono jG, Category.assoc, hc, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
      pullback.lift_fst, pullback.lift_snd, hs, inv_mul_cancel_right]

end Main

theorem torsion_exact : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Gt B : Over S) [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B] [IsCommMonObj B] (u : splitTorus S X ⟶ Gt) (q : Gt ⟶ B) [IsMonHom u] [IsMonHom q], Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback u (toUnit _) q η[B] → ∀ (N : ℕ), 1 ≤ N → ∀ (TN GN BN : Over S) (jT : TN ⟶ splitTorus S X) (jG : GN ⟶ Gt) (jB : BN ⟶ B) (eB : 𝟙_ _ ⟶ BN), IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[splitTorus S X] → IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt] → IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B] → eB ≫ jB = η[B] → ∀ (a : TN ⟶ GN) (b : GN ⟶ BN), a ≫ jG = jT ≫ u → b ≫ jB = jG ≫ q → Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit TN) b eB := by
  intro S X _ _ _ Gt B _ _ _ _ u q _ _ hfl hsu hqc hu N hN TN GN BN jT jG jB eB hT hG hB he a b ha hb
  have hN' : N ≠ 0 := by omega
  have hP := IsPullback.of_hasPullback q jB
  obtain ⟨φ, c, sq⟩ := exists_isPullback_cover hu hG hB hb hP.w
  have sql : IsPullback (pullback.fst φ ((𝟙 _) ^ N)).left c.left (pullback.snd q jB).left b.left :=
    sq.map (Over.forget S)
  have hPl : IsPullback (pullback.fst q jB).left (pullback.snd q jB).left q.left jB.left :=
    hP.map (Over.forget S)
  have hZl : IsPullback (pullback.snd φ ((𝟙 _) ^ N)).left (pullback.fst φ ((𝟙 _) ^ N)).left
      ((𝟙 (splitTorus S X)) ^ N).left φ.left :=
    (IsPullback.of_hasPullback φ ((𝟙 _) ^ N)).flip.map (Over.forget S)
  have f1 : Flat ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.flat_mulN S X hN'
  have s1 : Surjective ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.surjective_mulN S X hN'
  have f2 : Flat (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl f1
  have s2 : Surjective (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl s1
  have f3 : Flat (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hfl
  have s3 : Surjective (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hsu
  have c3 : QuasiCompact (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hqc
  refine ⟨?_, ?_, isPullback_kernel hu hT hG hB he ha hb⟩
  · haveI := GlobalTheory.flat_descendsAlong_fpqc
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sql ⟨⟨s3, f3⟩, c3⟩ f2
  · have : Surjective (c.left ≫ b.left) := by
      rw [← sql.w]; infer_instance
    exact Surjective.of_comp c.left b.left

end GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext
