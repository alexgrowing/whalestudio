import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationSheafGlueModulesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModulesGlueCoverStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizedModuleBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualModuleFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberPointsGlueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFin

theorem spMap_dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (dualMap d) ≫ spMap (dualMap c) = spMap (dualMap (d.comp c)) := by
  have : dualMap (d.comp c) = (dualMap d).comp (dualMap c) := by
    ext a <;> simp [dualMap]
  simp only [this, spMap, ← Spec.map_comp]
  rfl

theorem spMap_dual_id {A : Type} [CommRing A] : spMap (dualMap (RingHom.id A)) = 𝟙 _ := by
  have : dualMap (RingHom.id A) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  simp only [this, spMap]
  exact Spec.map_id _

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pt_left_inj {A : Type} [CommRing A] {a : Sp A ⟶ S} {E : Type} [AddCommGroup E] [Module A E]
    (M : LieModel G a E) {u v : E} (h : (M.pt u).left = (M.pt v).left) : u = v :=
  M.inj (Over.OverMorphism.ext h)

theorem exists_tr {A B : Type} [CommRing A] [CommRing B] (a : Sp A ⟶ S) (b : Sp B ⟶ S) (c : A →+* B)
    (h : spMap c ≫ a = b) {E E' : Type} [AddCommGroup E] [AddCommGroup E'] [Module A E] [Module B E']
    (M : LieModel G a E) (M' : LieModel G b E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear S G A B c a E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  simpa [LieModel.Lifts] using this

theorem exists_trL {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : Sp A ⟶ S) (b : Sp B ⟶ S) (c : A →+* B) (hc : ∀ r, c (algebraMap R A r) = algebraMap R B r)
    (h : spMap c ≫ a = b) {E E' : Type} [AddCommGroup E] [AddCommGroup E'] [Module A E] [Module B E']
    [Module R E] [Module R E'] [IsScalarTower R A E] [IsScalarTower R B E']
    (M : LieModel G a E) (M' : LieModel G b E') :
    ∃ j : E →ₗ[R] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  obtain ⟨j, hj⟩ := exists_tr a b c h M M'
  refine ⟨{ toFun := j, map_add' := j.map_add, map_smul' := fun r e => ?_ }, hj⟩
  have h1 : r • e = algebraMap R A r • e := (algebraMap_smul A r e).symm
  have h2 : r • j e = algebraMap R B r • j e := (algebraMap_smul B r (j e)).symm
  simp only [RingHom.id_apply]
  rw [h1, h2, j.map_smulₛₗ, hc]

theorem unit_of_dvd {R : Type} [CommRing R] {a g : R} (h : a ∣ g) :
    IsUnit (algebraMap R (Localization.Away g) a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit g)

def cmap {R : Type} [CommRing R] {g g' : R} (h : g ∣ g') :
    Localization.Away g →ₐ[R] Localization.Away g' :=
  IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := Algebra.ofId R (Localization.Away g'))
    (by
      rintro ⟨_, n, rfl⟩
      simpa [Algebra.ofId_apply] using (unit_of_dvd h).pow n)

theorem ringHom_unique {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {g : R}
    (a b : Localization.Away g →+* B) (ha : a.comp (algebraMap R _) = algebraMap R B)
    (hb : b.comp (algebraMap R _) = algebraMap R B) : a = b :=
  IsLocalization.ringHom_ext (Submonoid.powers g) (ha.trans hb.symm)

theorem unit_end {R A F : Type} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup F] [Module R F]
    [Module A F] [IsScalarTower R A F] {a : R} (h : IsUnit (algebraMap R A a)) :
    IsUnit (algebraMap R (Module.End R F) a) := by
  obtain ⟨u, hu⟩ := h
  have hinv : ∀ y : F, a • ((↑u⁻¹ : A) • y) = y := fun y => by
    rw [← algebraMap_smul A a, ← hu, smul_smul, Units.mul_inv, one_smul]
  have hinv' : ∀ y : F, (↑u⁻¹ : A) • (a • y) = y := fun y => by
    rw [← algebraMap_smul A a y, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [Module.End.isUnit_iff]
  refine ⟨fun y z hyz => ?_, fun y => ⟨(↑u⁻¹ : A) • y, ?_⟩⟩
  · have : a • y = a • z := by simpa [Module.algebraMap_end_apply] using hyz
    rw [← hinv' y, ← hinv' z, this]
  · simpa [Module.algebraMap_end_apply] using hinv y

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_dual_alg {A B : Type} [CommRing A] [CommRing B] (c : A →+* B) :
    spMap (dualMap c) ≫ spMap (algebraMap A (DualNumber A)) =
      spMap (algebraMap B (DualNumber B)) ≫ spMap c := by
  rw [spMap_comp', spMap_comp']
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_fst_dual {A B : Type} [CommRing A] [CommRing B] (c : A →+* B) :
    spMap c ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom =
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap c) := by
  rw [spMap_comp', spMap_comp']
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

abbrev Idx {R J : Type} [CommRing R] (f : J → R) : Type := {g : R // ∃ i, f i ∣ g}

abbrev ptAt {R : Type} [CommRing R] (x : Sp R ⟶ S) (g : R) : Sp (Localization.Away g) ⟶ S :=
  spMap (algebraMap R (Localization.Away g)) ≫ x

theorem cmap_alg {R : Type} [CommRing R] {g g' : R} (h : g ∣ g') :
    (cmap h).toRingHom.comp (algebraMap R (Localization.Away g)) = algebraMap R (Localization.Away g') :=
  RingHom.ext (cmap h).commutes

theorem pt_cmap {R : Type} [CommRing R] (x : Sp R ⟶ S) {g g' : R} (h : g ∣ g') :
    spMap (cmap h).toRingHom ≫ ptAt x g = ptAt x g' := by
  rw [← Category.assoc, spMap_comp', cmap_alg]

theorem cmap_self {R : Type} [CommRing R] {g : R} (h : g ∣ g) : (cmap h).toRingHom = RingHom.id _ :=
  ringHom_unique (R := R) _ _ (cmap_alg h) rfl

theorem cmap_comp {R : Type} [CommRing R] {g g' g'' : R} (h : g ∣ g') (h' : g' ∣ g'') (h'' : g ∣ g'') :
    (cmap h').toRingHom.comp (cmap h).toRingHom = (cmap h'').toRingHom :=
  ringHom_unique (R := R) _ _ (by rw [RingHom.comp_assoc, cmap_alg, cmap_alg]) (cmap_alg h'')

theorem loc_of_family {R : Type} [CommRing R] (x : Sp R ⟶ S) {J : Type} [Finite J] (f : J → R)
    (hf : Ideal.span (Set.range f) = ⊤) {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E)
    (F : Idx f → Type) [∀ g, AddCommGroup (F g)] [∀ g, Module R (F g)]
    [∀ g : Idx f, Module (Localization.Away g.1) (F g)]
    [∀ g : Idx f, IsScalarTower R (Localization.Away g.1) (F g)]
    (mg : ∀ g : Idx f, LieModel G (ptAt x g.1) (F g))
    (hqc : ∀ (g g' : Idx f) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → ∀ r : F g →ₗ[R] F g',
      (∀ y, ((mg g').pt (r y)).left = spMap (dualMap (cmap h).toRingHom) ≫ ((mg g).pt y).left) →
      IsLocalizedModule (Submonoid.powers t) r) :
    ∃ ρ : ∀ g, E →ₗ[R] F g,
      (∀ g e, ((mg g).pt (ρ g e)).left = spMap (dualMap (algebraMap R (Localization.Away g.1))) ≫ (M.pt e).left) ∧
      ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (ρ ⟨f i, i, dvd_rfl⟩) := by
  have hres : ∀ (g g' : Idx f) (h : g.1 ∣ g'.1), ∃ r : F g →ₗ[R] F g', ∀ y,
      ((mg g').pt (r y)).left = spMap (dualMap (cmap h).toRingHom) ≫ ((mg g).pt y).left :=
    fun g g' h => exists_trL (R := R) _ _ (cmap h).toRingHom (cmap h).commutes (pt_cmap x h) (mg g) (mg g')
  choose res hres using hres
  have hρ : ∀ g : Idx f, ∃ r : E →ₗ[R] F g, ∀ e,
      ((mg g).pt (r e)).left = spMap (dualMap (algebraMap R (Localization.Away g.1))) ≫ (M.pt e).left :=
    fun g => exists_trL (R := R) x (ptAt x g.1) (algebraMap R _) (fun _ => rfl) rfl M (mg g)
  choose ρ hρ using hρ
  have hglue := fun X => GlobalTheory.T.dual_number_points_glue X R J f hf
  refine ⟨ρ, hρ, GlobalTheory.T.localization_sheaf_glue_modules R E J f hf F res ρ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro g h y
    apply pt_left_inj (mg g)
    rw [hres, cmap_self, spMap_dual_id, Category.id_comp]
  · intro g g' g'' h h' h'' y
    apply pt_left_inj (mg g'')
    rw [hres, hres, hres, ← Category.assoc, spMap_dual_comp, cmap_comp h h' h'']
  · intro g g' h e
    apply pt_left_inj (mg g')
    rw [hres, hρ, hρ, ← Category.assoc, spMap_dual_comp, cmap_alg]
  · intro g a h
    obtain ⟨i, -⟩ := g.2
    exact unit_end (A := Localization.Away g.1) (unit_of_dvd h)
  · intro g g' h t ht
    exact hqc g g' h t ht _ (hres g g' h)
  · intro e he
    refine pt_left_inj M (v := 0) ((hglue G.left).2.1 _ _ fun i => ?_)
    have h1 := hρ ⟨f i, i, dvd_rfl⟩ e
    have h2 := hρ ⟨f i, i, dvd_rfl⟩ 0
    rw [he i] at h1
    rw [map_zero] at h2
    exact h1.symm.trans h2
  · intro w hw
    obtain ⟨v0, hv0⟩ := (hglue G.left).2.2 (fun i => ((mg ⟨f i, i, dvd_rfl⟩).pt (w i)).left) (by
      intro i j a b ha hb
      have ea : a = (cmap (dvd_mul_right (f i) (f j))).toRingHom :=
        ringHom_unique (R := R) _ _ ha (cmap_alg _)
      have eb : b = (cmap (dvd_mul_left (f j) (f i))).toRingHom :=
        ringHom_unique (R := R) _ _ hb (cmap_alg _)
      subst ea eb
      have h1 := hres ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (w i)
      have h2 := hres ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (w j)
      rw [hw i j] at h1
      exact h1.symm.trans h2)
    have hover : v0 ≫ G.hom = (epsAt x).hom := by
      refine (hglue S).2.1 _ _ fun i => ?_
      rw [← Category.assoc, hv0 i]
      have h1 := Over.w ((mg ⟨f i, i, dvd_rfl⟩).pt (w i))
      refine h1.trans ?_
      have h2 := spMap_dual_alg (algebraMap R (Localization.Away (f i)))
      simp only [epsAt, Over.mk_hom]
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ x) h2.symm
    have htan : IsTanAt G x (Over.homMk v0 hover : epsAt x ⟶ G) := by
      refine (hglue G.left).1 _ _ fun i => ?_
      have h1 := (mg ⟨f i, i, dvd_rfl⟩).tan (w i)
      have h2 := spMap_fst_dual (algebraMap R (Localization.Away (f i)))
      let u : Over.mk (ptAt x (f i)) ⟶ Over.mk x := Over.homMk (spMap (algebraMap R _)) rfl
      have h3 : u ≫ (1 : Over.mk x ⟶ G) = 1 := MonObj.comp_one u
      have h4 := congrArg (fun q => q.left) h3
      simp only [Over.comp_left] at h4
      refine Eq.trans ?_ (h1.trans h4.symm)
      simp only [Over.homMk_left]
      rw [← Category.assoc]
      refine (congrArg (· ≫ v0) h2).trans ?_
      simp only [Category.assoc]
      rw [hv0 i]
    obtain ⟨e, he⟩ := M.onto _ htan
    refine ⟨e, fun i => pt_left_inj (mg ⟨f i, i, dvd_rfl⟩) ?_⟩
    refine (hρ ⟨f i, i, dvd_rfl⟩ e).trans ?_
    rw [he]
    exact hv0 i

theorem exists_equiv {R C : Type} [CommRing R] [CommRing C] [Algebra R C] (a : Sp C ⟶ S)
    {E E' : Type} [AddCommGroup E] [AddCommGroup E'] [Module C E] [Module C E'] [Module R E] [Module R E']
    [IsScalarTower R C E] [IsScalarTower R C E'] (M : LieModel G a E) (M' : LieModel G a E') :
    ∃ e : E ≃ₗ[R] E', ∀ y, (M'.pt (e y)).left = (M.pt y).left := by
  have hid : spMap (RingHom.id C) ≫ a = a := by
    have : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨j, hj⟩ := exists_trL (R := R) a a (RingHom.id C) (fun _ => rfl) hid M M'
  obtain ⟨k, hk⟩ := exists_trL (R := R) a a (RingHom.id C) (fun _ => rfl) hid M' M
  simp only [spMap_dual_id, Category.id_comp] at hj hk
  refine ⟨LinearEquiv.ofLinear j k ?_ ?_, hj⟩
  · refine LinearMap.ext fun y => pt_left_inj M' ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [hj, hk]
  · refine LinearMap.ext fun y => pt_left_inj M ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [hk, hj]

theorem cmap_loc {R : Type} [CommRing R] {g g' t : R} (h : g ∣ g') (ht : g' = g * t) :
    IsLocalizedModule (Submonoid.powers t) (cmap h).toLinearMap := by
  subst ht
  have hgB : IsUnit (algebraMap R (Localization.Away (g * t)) g) := unit_of_dvd h
  have htB : IsUnit (algebraMap R (Localization.Away (g * t)) t) := unit_of_dvd (dvd_mul_left t g)
  have hgA : IsUnit (algebraMap R (Localization.Away g) g) := IsLocalization.Away.algebraMap_isUnit g
  have hc : ∀ r, cmap h (algebraMap R (Localization.Away g) r) = algebraMap R (Localization.Away (g * t)) r :=
    (cmap h).commutes
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine unit_end (A := Localization.Away (g * t)) ?_
    simpa using htB.pow n
  · intro y
    obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj (g * t) y
    refine ⟨(IsLocalization.mk' (Localization.Away g) a (⟨g ^ n, n, rfl⟩ : Submonoid.powers g),
      ⟨t ^ n, n, rfl⟩), ?_⟩
    have hmk := IsLocalization.mk'_spec (Localization.Away g) a (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    have h1 := congrArg (cmap h) hmk
    rw [map_mul, hc, hc] at h1
    simp only at h1
    change t ^ n • y = cmap h _
    refine (hgB.pow n).mul_right_cancel ?_
    rw [Algebra.smul_def]
    rw [map_pow] at h1 ⊢
    rw [h1, ← hy, map_mul, mul_pow]
    ring
  · intro x₁ x₂ he
    have hz : cmap h (x₁ - x₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact he
    obtain ⟨n, a, hy⟩ := IsLocalization.Away.surj g (x₁ - x₂)
    have h0 : algebraMap R (Localization.Away (g * t)) a = 0 := by
      have h1 := congrArg (cmap h) hy
      rw [map_mul, hz, zero_mul, hc] at h1
      exact h1.symm
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (g * t)) _ a).1 h0
    refine ⟨⟨t ^ k, k, rfl⟩, ?_⟩
    change t ^ k • x₁ = t ^ k • x₂
    rw [← sub_eq_zero, ← smul_sub]
    have h2 : algebraMap R (Localization.Away g) ((g * t) ^ k * a) = 0 := by
      simp only at hk
      rw [hk, map_zero]
    refine ((hgA.pow (k + n)).mul_left_eq_zero).1 ?_
    rw [Algebra.smul_def, map_mul, map_pow, map_mul, mul_pow, ← hy] at *
    rw [pow_add]
    linear_combination h2

theorem fin_of_charts {R : Type} [CommRing R] (x : Sp R ⟶ S) {J : Type} [Finite J] (f : J → R)
    (hf : Ideal.span (Set.range f) = ⊤) {E : Type} [AddCommGroup E] [Module R E]
    (P : J → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
    [∀ i, Module (Localization.Away (f i)) (P i)] [∀ i, IsScalarTower R (Localization.Away (f i)) (P i)]
    [∀ i, Module.Finite (Localization.Away (f i)) (P i)] [∀ i, Module.Projective (Localization.Away (f i)) (P i)]
    (m : ∀ i (C : Type) [CommRing C] [Algebra R C], IsUnit (algebraMap R C (f i)) →
      LieModel G (spMap (algebraMap R C) ≫ x) (P i →ₗ[R] C))
    (nat : ∀ i (C C' : Type) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (hC : IsUnit (algebraMap R C (f i))) (hC' : IsUnit (algebraMap R C' (f i))) (c : C →ₐ[R] C')
      (w : P i →ₗ[R] C),
      ((m i C' hC').pt (c.toLinearMap ∘ₗ w)).left = spMap (dualMap c.toRingHom) ≫ ((m i C hC).pt w).left)
    (M : LieModel G x E) : Module.Finite R E ∧ Module.Projective R E := by
  have hix : ∀ g : Idx f, ∃ i, f i ∣ g.1 := fun g => g.2
  choose ix hix using hix
  have hqc : ∀ (g g' : Idx f) (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t →
      ∀ r : (P (ix g) →ₗ[R] Localization.Away g.1) →ₗ[R] (P (ix g') →ₗ[R] Localization.Away g'.1),
      (∀ y, ((m (ix g') _ (unit_of_dvd (hix g'))).pt (r y)).left =
        spMap (dualMap (cmap h).toRingHom) ≫ ((m (ix g) _ (unit_of_dvd (hix g))).pt y).left) →
      IsLocalizedModule (Submonoid.powers t) r := by
    intro g g' h t ht r hr
    have hu' : IsUnit (algebraMap R (Localization.Away g'.1) (f (ix g))) :=
      unit_of_dvd ((hix g).trans h)
    obtain ⟨e, he⟩ := exists_equiv (R := R) (ptAt x g'.1) (m (ix g) _ hu') (m (ix g') _ (unit_of_dvd (hix g')))
    haveI := cmap_loc h ht
    haveI hcr := GlobalTheory.T.localized_module_base_change R (P (ix g)) (Localization.Away g.1) (Localization.Away g'.1) (f (ix g)) t
      (unit_of_dvd (hix g)) (cmap h) (cmap_loc h ht)
    have hrr : r = (e : _ →ₗ[R] _) ∘ₗ LinearMap.compRight R (cmap h).toLinearMap := by
      refine LinearMap.ext fun y => pt_left_inj (m (ix g') _ (unit_of_dvd (hix g'))) ?_
      rw [hr]
      refine Eq.trans ?_ (he _).symm
      exact (nat (ix g) _ _ (unit_of_dvd (hix g)) hu' (cmap h) y).symm
    rw [hrr]
    exact IsLocalizedModule.of_linearEquiv _ _ _
  obtain ⟨ρ, -, hloc⟩ := loc_of_family x f hf M (fun g => P (ix g) →ₗ[R] Localization.Away g.1)
    (fun g => m (ix g) _ (unit_of_dvd (hix g))) hqc
  have hcmp : ∀ i, ∃ _ : (P (ix ⟨f i, i, dvd_rfl⟩) →ₗ[R] Localization.Away (f i)) ≃ₗ[R]
      (P i →ₗ[R] Localization.Away (f i)), True := fun i => by
    obtain ⟨e, -⟩ := exists_equiv (R := R) (ptAt x (f i))
      (m (ix ⟨f i, i, dvd_rfl⟩) _ (unit_of_dvd (hix ⟨f i, i, dvd_rfl⟩)))
      (m i _ (unit_of_dvd (dvd_refl (f i))))
    exact ⟨e, trivial⟩
  choose e _ using hcmp
  haveI : ∀ i, Module.Finite (Localization.Away (f i)) (P i →ₗ[R] Localization.Away (f i)) :=
    fun i => (GlobalTheory.T.dual_module_finite_projective R (P i) (f i)).1
  haveI : ∀ i, Module.Projective (Localization.Away (f i)) (P i →ₗ[R] Localization.Away (f i)) :=
    fun i => (GlobalTheory.T.dual_module_finite_projective R (P i) (f i)).2
  refine GlobalTheory.T.projective_modules_glue_cover R E J f hf (fun i => P i →ₗ[R] Localization.Away (f i))
    (fun i => (e i : _ →ₗ[R] _) ∘ₗ ρ ⟨f i, i, dvd_rfl⟩) fun i => ?_
  haveI := hloc i
  exact IsLocalizedModule.of_linearEquiv _ _ _

end GlobalTheory.CompanionTheory.Ar.LieFin

theorem GlobalTheory.CompanionTheory.Ar.LieFin.lieModel_finite_projective :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (J : Type) [Finite J] (f : J → R),
      Ideal.span (Set.range f) = ⊤ → (∀ i, LieChart G x (f i)) →
      ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E := by
  intro S G _ R _ x J _ f hf hch E _ _ M
  choose P iA iM iL ist ifin iproj m nat using hch
  exact @GlobalTheory.CompanionTheory.Ar.LieFin.fin_of_charts S G _ R _ x J _ f hf E _ _ P iA iM iL ist ifin iproj m nat M
