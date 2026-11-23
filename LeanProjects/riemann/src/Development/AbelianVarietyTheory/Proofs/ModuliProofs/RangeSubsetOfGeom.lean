import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {S : Scheme.{0}}

def ClopenCond (T : Over S) (P : ∀ T' : Over S, (T' ⟶ T) → Prop) : Prop :=
  ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), P T' h ↔ Set.range h.left ⊆ U

theorem ClopenCond.congr {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (e : ∀ T' h, P' T' h ↔ P T' h) : ClopenCond T P' := by
  obtain ⟨U, hU, H⟩ := h
  exact ⟨U, hU, fun T' h => (e T' h).trans (H T' h)⟩

theorem ClopenCond.and {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (h' : ClopenCond T P') : ClopenCond T fun T' h => P T' h ∧ P' T' h := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  refine ⟨U ⊓ U', hU.inter hU', fun T' h => ?_⟩
  beta_reduce
  rw [H, H', TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]

theorem ClopenCond.forall_finite {T : Over S} {J : Type} [Finite J] {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop}
    (h : ∀ i, ClopenCond T (P i)) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  choose U hU H using h
  refine ⟨⟨⋂ i, (U i : Set T.left), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, isClosed_iInter hU,
    fun T' h => ?_⟩
  simp only [H, TopologicalSpace.Opens.coe_mk, Set.subset_iInter_iff]

theorem ClopenCond.forall_of_finite {T : Over S} {J κ : Type} [Finite κ] (q : J → κ)
    {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ∀ i, ClopenCond T (P i))
    (hq : ∀ i j, q i = q j → ∀ T' h, P i T' h → P j T' h) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  refine (ClopenCond.forall_finite (J := Set.range q) fun c => h c.2.choose).congr fun T' h => ?_
  exact ⟨fun H c => H _, fun H i => hq _ _ (⟨i, rfl⟩ : q i ∈ Set.range q).choose_spec T' h (H ⟨q i, i, rfl⟩)⟩

theorem exists_finite_mod (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    ∃ (κ : Type) (_ : Finite κ) (q : M → κ), ∀ a a', q a = q a' → ∃ c, a' = a + n • c := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let b := Module.Free.chooseBasis ℤ M
  refine ⟨Module.Free.ChooseBasisIndex ℤ M → ZMod n, inferInstance, fun a i => (b.repr a i : ZMod n),
    fun a a' h => ?_⟩
  have h1 : ∀ i, ∃ c : ℤ, b.repr a' i - b.repr a i = n * c := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h i)
  choose c hc using h1
  refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
  rw [map_add, map_nsmul, LinearEquiv.apply_symm_apply]
  simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  linarith [hc i]

theorem clopenCond_eq {T Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (u u' : T ⟶ Z) :
    ClopenCond T fun _ h => h ≫ u = h ≫ u' := by
  refine ⟨(FinEt.agreeι u u').opensRange, (FinEt.agreeι u u').isClosedEmbedding.isClosed_range, fun T' h => ?_⟩
  refine Iff.trans ?_ (FinEt.comp_eq_comp_iff_range u u' h.left)
  exact ⟨fun e => congrArg CommaMorphism.left e, fun e => Over.OverMorphism.ext e⟩

def RepTors (G : Over S) [GrpObj G] (n : ℕ) (La : Type) [AddCommGroup La] (Z : Over S) (et : La → (Z ⟶ G)) : Prop :=
  IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧
    ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) →
      ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a

theorem RepTors.ext {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S} {et : La → (Z ⟶ G)}
    (R : RepTors G n La Z et) {T : Over S} {u u' : T ⟶ Z} (h : ∀ a, u ≫ et a = u' ≫ et a) : u = u' :=
  (R.2.2.2.2 T (fun a => u' ≫ et a) (fun a c => by rw [R.2.2.1, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one])).unique h fun _ => rfl

theorem RepTors.clopenCond {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S}
    {et : La → (Z ⟶ G)} (R : RepTors G n La Z et) {T : Over S} (x y : La → (T ⟶ G))
    (hx : ∀ a c, x (a + c) = x a * x c) (hx' : ∀ a, x a ^ n = 1)
    (hy : ∀ a c, y (a + c) = y a * y c) (hy' : ∀ a, y a ^ n = 1) :
    ClopenCond T fun _ h => ∀ a, h ≫ x a = h ≫ y a := by
  obtain ⟨u, hu, -⟩ := R.2.2.2.2 T x hx hx'
  obtain ⟨u', hu', -⟩ := R.2.2.2.2 T y hy hy'
  have := R.1
  have := R.2.1
  refine (clopenCond_eq u u').congr fun T' h => ⟨fun H => R.ext fun a => ?_, fun H a => ?_⟩
  · rw [Category.assoc, Category.assoc, hu, hu', H]
  · rw [← hu, ← hu', ← Category.assoc, H, Category.assoc]

theorem exists_lift_geom {W Z : Scheme.{0}} (p : W ⟶ Z) [IsFinite p] {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z) (hz : Set.range z ⊆ Set.range p) : ∃ w : Sp k ⟶ W, w ≫ p = z := by
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  have h1 : pt ∈ Set.range (pullback.snd p z) := by
    rw [Scheme.Pullback.range_snd]
    exact hz ⟨pt, rfl⟩
  obtain ⟨y, -⟩ := h1
  have : Nonempty (pullback p z : Scheme) := ⟨y⟩
  have : IsAffine (pullback p z) := isAffine_of_isAffineHom (pullback.snd p z)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := (pullback p z : Scheme))).exists_closed_singleton Set.univ_nonempty
  refine ⟨pointOfClosedPoint (pullback.snd p z) x hx ≫ pullback.fst p z, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem exists_image {W Z : Over S} [IsFinite W.hom] [Etale W.hom] [IsFinite Z.hom] [Etale Z.hom] (p : W ⟶ Z) :
    ∃ U : Z.left.Opens, IsClosed (U : Set Z.left) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
      (z : Over.mk x ⟶ Z), Set.range z.left ⊆ U ↔ ∃ w : Over.mk x ⟶ W, w ≫ p = z := by
  have := FinEt.isFinite_left p
  have := FinEt.etale_left p
  refine ⟨⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩, p.left.isClosedMap.isClosed_range,
    fun k _ _ x z => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_lift_geom p.left z.left h
    refine ⟨Over.homMk w ?_, Over.OverMorphism.ext hw⟩
    show w ≫ W.hom = x
    rw [← Over.w p, ← Category.assoc, hw]
    exact Over.w z
  · rintro ⟨w, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨w.left y, by simp⟩

theorem exists_sub {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (U : Z.left.Opens) (hU : IsClosed (U : Set Z.left)) :
    ∃ (V : Over S) (i : V ⟶ Z), IsFinite V.hom ∧ Etale V.hom ∧ Mono i ∧
      ∀ (T : Over S) (h : T ⟶ Z), Set.range h.left ⊆ U ↔ ∃ h' : T ⟶ V, h' ≫ i = h := by
  have hc : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  refine ⟨Over.mk (U.ι ≫ Z.hom), Over.homMk U.ι rfl, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)),
    inferInstanceAs (Etale (U.ι ≫ Z.hom)), ?_, fun T h => ?_⟩
  · have : Mono (Over.homMk U.ι rfl : Over.mk (U.ι ≫ Z.hom) ⟶ Z).left := inferInstanceAs (Mono U.ι)
    exact Over.mono_of_mono_left _
  · rw [FinEt.range_subset_iff_factors]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
      show t ≫ U.ι ≫ Z.hom = T.hom
      rw [← Category.assoc, ht, Over.w h]
    · rintro ⟨t, ht⟩
      exact ⟨t.left, congrArg CommaMorphism.left ht⟩

theorem range_subset_of_geom {T Z : Over S} (h : T ⟶ Z) (U : Set Z.left)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ T), Set.range (y ≫ h).left ⊆ U) :
    Set.range h.left ⊆ U := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T.left t
  obtain ⟨p, rfl⟩ : t ∈ Set.range a := by rw [ha]; rfl
  exact H k (a ≫ T.hom) (Over.homMk a rfl) ⟨p, by simp⟩

theorem finiteEtale_tensor (X Y : Over S) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsFinite (X ⊗ Y).hom ∧ Etale (X ⊗ Y).hom :=
  ⟨inferInstanceAs (IsFinite (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (Etale (pullback.fst X.hom Y.hom ≫ X.hom))⟩

end GlobalTheory.LevCover
