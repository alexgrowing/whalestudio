import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBallQuotientEqSumMulFdeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclicStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonOfForallIsMaximalSmulEqZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverField
open GlobalTheory.CechPic

def Ac {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) : Prop :=
  ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    (cechLB f M D).Acyclic

theorem Ac.of_iso {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)}
    {f' : Y' ⟶ Spec (CommRingCat.of R)} {M : LB Y} {M' : LB Y'} (h : Ac f M) (hM : M.IsLB) (hM' : M'.IsLB)
    (e : Y' ⟶ Y) [IsIso e] (w : e ≫ f = f') (hc : CechPic.pull e (cls M hM) = cls M' hM') : Ac f' M' := by
  intro κ _ _ D hD hcov
  subst w
  have hD' : (fun i => e ⁻¹ᵁ (inv e ⁻¹ᵁ D i)) = D := funext fun i => by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]; rfl
  obtain ⟨φ⟩ := cechLB_pull_iso_of_isOpenImmersion R Y f M Y' e κ (fun i => inv e ⁻¹ᵁ D i) hM
    (fun i => by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
  rw [hD'] at φ
  obtain ⟨u, hu⟩ := (cls_eq_iff (pull_isLB hM e) hM').1 hc
  have H := h κ (fun i => inv e ⁻¹ᵁ D i) (fun i => (hD i).preimage_of_isIso _)
    (by rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)
  exact fun n => (H n).of_iso (φ.symm ≪≫ cechLBCongr _ D (pull_isLB hM e) hM' u hu)

theorem not_ac_of_cls_eq_zero {R : Type} [CommRing R] {Y : Scheme.{0}} [CompactSpace Y] [Nonempty Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y} (hM : M.IsLB) (h : cls M hM = 0) : ¬ Ac f M := by
  intro H
  have hO := Inh.trivLB_isLB Y
  have H' : Ac f (Inh.trivLB Y) := H.of_iso hM hO (𝟙 Y) (Category.id_comp _)
    (by rw [pull_id, h]; exact ((cls_eq_zero_iff hO).2 (triv_trivLB Y)).symm)
  obtain ⟨n, D, hD, hc⟩ := PrimVan.exists_fin_affine_cover Y
  have h0 := H' _ D hD hc 0
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h0
  have h1 : Subsingleton Γ(Y, ⊤) := ((PrimVan.homologyZeroEquiv f _ hc).toEquiv.trans
    ((SecOnR.of f _ ⊤).symm.toEquiv.trans (secOnTrivEquiv ⊤).toEquiv)).symm.subsingleton
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.arbitrary Y, trivial⟩⟩
  exact false_of_nontrivial_of_subsingleton Γ(Y, ⊤)

theorem pic_field {K : Type} [Field K] (c : CechPic.Pic (Spec (CommRingCat.of K))) : c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨i, hi⟩ := exists_chart hM (IsLocalRing.closedPoint K)
  rw [← pull_id (cls M hM)]
  refine (cls_eq_zero_iff (pull_isLB hM _)).2 ?_
  exact AbSquare.exists_gen_of_mem_chart hM _ _ (fun _ => i) fun _ z => by
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hi

section Family

variable {K : Type} [Field K] {A Z : Scheme.{0}} {g : A ⟶ Spec (CommRingCat.of K)} {p q : Z ⟶ A}
  {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ A} {Y : Scheme.{0}} {π : Y ⟶ Z}
  {f : Y ⟶ Spec (CommRingCat.of R)} {F : LB Z}

theorem ac_fibre_iff (hpq : IsPullback p q g g) (hπ : IsPullback π f p t) (hF : F.IsLB) (χ : R →+* K)
    (hχ : (Spec.map (CommRingCat.ofHom χ) ≫ t) ≫ g = 𝟙 _) (s : A ⟶ Z)
    (hp : s ≫ p = g ≫ Spec.map (CommRingCat.ofHom χ) ≫ t) (hq : s ≫ q = 𝟙 A)
    {Y₀ : Scheme.{0}} {π₀ : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Spec (CommRingCat.of K)}
    (h₀ : IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom χ))) :
    Ac f₀ ((F.pull π).pull π₀) ↔ Ac g (F.pull s) := by
  have h₁ := (h₀.paste_horiz hπ).paste_horiz hpq.flip
  rw [hχ] at h₁
  have : IsIso ((π₀ ≫ π) ≫ q) := h₁.isIso_fst_of_isIso
  have w : ((π₀ ≫ π) ≫ q) ≫ g = f₀ := h₁.w.trans (Category.comp_id _)
  have e : ((π₀ ≫ π) ≫ q) ≫ s = π₀ ≫ π := by
    refine hpq.hom_ext ?_ ?_
    · rw [Category.assoc, hp, ← Category.assoc, w]
      exact (h₀.paste_horiz hπ).w.symm
    · rw [Category.assoc, hq, Category.comp_id]
  have hc : CechPic.pull ((π₀ ≫ π) ≫ q) (cls _ (pull_isLB hF s)) = cls _ (pull_isLB (pull_isLB hF π) π₀) := by
    rw [cls_pull hF, cls_pull (pull_isLB hF π), cls_pull hF, ← pull_comp, ← pull_comp, e]
  refine ⟨fun H => H.of_iso (pull_isLB (pull_isLB hF π) π₀) (pull_isLB hF s)
    (inv ((π₀ ≫ π) ≫ q)) ?_ ?_, fun H => H.of_iso _ _ _ w hc⟩
  · rw [← w, IsIso.inv_hom_id_assoc]
  · rw [← hc, ← pull_comp, IsIso.inv_hom_id, pull_id]

variable [IsAlgClosed K] [Smooth g]

omit [IsAlgClosed K] in

theorem family_fibres
    (hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f g u → IsProjBy f)
    (hpq : IsPullback p q g g) (hπ : IsPullback π f p t) [IsOpenImmersion t] :
    IsNoetherianRing R ∧ Flat f ∧ IsProjBy f := by
  have h := hπ.paste_horiz hpq.flip
  refine ⟨?_, MorphismProperty.of_isPullback (P := @Flat) h inferInstance, hproj _ _ _ _ _ h⟩
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (t ≫ g)
  exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).1 inferInstance

theorem ac_of_slices
    (hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f g u → IsProjBy f)
    (hpq : IsPullback p q g g) (hπ : IsPullback π f p t) [IsOpenImmersion t] (hF : F.IsLB)
    (H : ∀ x : Spec (CommRingCat.of K) ⟶ A, x ≫ g = 𝟙 _ → (∀ a, ∃ y, t y = x a) →
      ∃ s : A ⟶ Z, s ≫ p = g ≫ x ∧ s ≫ q = 𝟙 A ∧ Ac g (F.pull s)) : Ac f (F.pull π) := by
  obtain ⟨hN, hfl, hpr⟩ := family_fibres hproj hpq hπ
  refine (cechLB_acyclic_iff_fibres R Y f hfl hpr _ (pull_isLB hF π)).1 fun P hP => ?_
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ g)
  have hft : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (by rw [hφ]; infer_instance)
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hft
  obtain ⟨χ, hker⟩ := GlobalTheory.PointSupport.exists_algHom_ker_eq K R P
  have hχ : (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ t) ≫ g = 𝟙 _ := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext k
    exact χ.commutes k
  obtain ⟨s, hp, hq, hs⟩ := H _ hχ fun a => ⟨_, rfl⟩
  exact ⟨K, inferInstance, χ.toRingHom, hker, fun Y₀ π₀ f₀ h₀ =>
    (ac_fibre_iff hpq hπ hF _ hχ s hp hq h₀).2 hs⟩

omit [IsAlgClosed K] in

theorem ac_slice
    (hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f g u → IsProjBy f)
    (hpq : IsPullback p q g g) (hF : F.IsLB)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ A) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → Ac f (F.pull π))
    (x : Spec (CommRingCat.of K) ⟶ A) (hx : x ≫ g = 𝟙 _) (s : A ⟶ Z) (hp : s ≫ p = g ≫ x) (hq : s ≫ q = 𝟙 A) :
    Ac g (F.pull s) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := A.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint K))) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let t : Spec (CommRingCat.of Γ(A, U)) ⟶ A := IsAffineOpen.fromSpec hU
  have : IsOpenImmersion t := inferInstanceAs (IsOpenImmersion (IsAffineOpen.fromSpec hU))
  have hr : Set.range x ⊆ Set.range t := by
    rintro _ ⟨a, rfl⟩
    have : a = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact (IsAffineOpen.range_fromSpec hU).ge hxU
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift t x hr)
  have e : Spec.map (CommRingCat.ofHom φ.hom) ≫ t = x :=
    (congrArg (· ≫ t) hφ).trans (IsOpenImmersion.lift_fac t x hr)
  have hπ := IsPullback.of_hasPullback p t
  obtain ⟨hN, hfl, hpr⟩ := family_fibres hproj hpq hπ
  have h₀ := IsPullback.of_hasPullback (pullback.snd p t) (Spec.map (CommRingCat.ofHom φ.hom))
  exact (ac_fibre_iff hpq hπ hF φ.hom (by rw [e, hx]) s (by rw [e, hp]) hq h₀).1
    ((cechLB_acyclic_iff_fibres _ _ _ hfl hpr _ (pull_isLB hF _)).2 (H _ t _ _ _ hπ this) K φ.hom _ _ _ h₀)

end Family

section Group

variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))} [GrpObj B]

omit [GrpObj B] in

theorem pull_const (c : CechPic.Pic B.left) (T : Over (Spec (CommRingCat.of K))) (x : 𝟙_ _ ⟶ B) :
    CechPic.pull (toUnit T ≫ x).left c = 0 := by
  rw [Over.comp_left, pull_comp]
  exact (congrArg _ (pic_field _)).trans (map_zero _)

theorem lam_const (c : CechPic.Pic B.left) {T : Over (Spec (CommRingCat.of K))} (x : 𝟙_ _ ⟶ B) (y : T ⟶ B) :
    lam c (toUnit T ≫ x) y = CechPic.pull ((toUnit T ≫ x) * y).left c - CechPic.pull y.left c := by
  rw [lam, pull_const, sub_zero]
  exact (congrArg _ (pull_const c T η[B])).trans (add_zero _)

theorem lam_sub (c c' : CechPic.Pic B.left) {T : Over (Spec (CommRingCat.of K))} (x y : T ⟶ B) :
    lam (c - c') x y = lam c x y - lam c' x y := by
  simp only [lam, map_sub]; abel

variable [IsCommMonObj B] {L : LB B.left}

theorem lam_lam (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen) (x : 𝟙_ _ ⟶ B)
    {T : Over (Spec (CommRingCat.of K))} (u v : T ⟶ B) :
    lam (lam (cls L hL) (toUnit B ≫ x) (𝟙 B)) u v = 0 := by
  have e : ∀ w : T ⟶ B, CechPic.pull w.left (lam (cls L hL) (toUnit B ≫ x) (𝟙 B)) =
      lam (cls L hL) w (toUnit T ≫ x) := fun w => by
    rw [pull_lam, Category.comp_id, ← Category.assoc, comp_toUnit, lam_comm]
  rw [lam, e, e, e, e, lam_mul_left hL hΘ, lam_one_left]
  abel

theorem eq_one_of_lam_eq_zero (hL : L.IsLB) (hK : KTriv B L) (x : 𝟙_ _ ⟶ B)
    (h : lam (cls L hL) (toUnit B ≫ x) (𝟙 B) = 0) : x = 1 := by
  refine InK.eq_one hK fun p => ⟨⊤, trivial, ?_⟩
  have hD : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  have e := congrArg (CechPic.pull (snd (𝟙_ _) B).left) h
  rw [pull_lam, map_zero, Category.comp_id, ← Category.assoc, comp_toUnit, lam_const,
    toUnit_unique (toUnit _) (fst (𝟙_ _) B)] at e
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ e)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

theorem ac_of_primitive [IsAlgClosed K] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {M : LB B.left}
    (hM : M.IsLB) (h : lam (cls M hM) (fst B B) (snd B B) = 0) (hne : cls M hM ≠ 0) : Ac B.hom M :=
  GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed K B hB hp M hM
    ((cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ((cls_cube_two hM _ _ (LB.isLB_linComb hM _ _)).trans h))
    fun ht => hne ((cls_eq_zero_iff hM).2 ht)

end Group

theorem exists_point_translate : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL K _ _ P O hO hu
  by_contra hno
  have := P.isAb.smooth
  have := P.isAb.proper
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom u → IsProjBy f := by
    intro R _ u X π f h
    obtain ⟨N, -, m, s, h₁, h₂⟩ := polAV_veryAmpleBy hL.polBaseChange _ P R u X π f h
    exact ⟨_, h₁, m, s, h₂⟩
  have hpr : IsProjBy P.A.hom := hproj K (𝟙 _) _ (𝟙 _) _ (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
    obtain ⟨r, hr⟩ := P.rigid
    obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
    exact ⟨c.t, c.isGen⟩
  have lamO : lam (cls O hO) (fst P.A P.A) (snd P.A P.A) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) -
    CechPic.pull (snd P.A P.A).left (cls O hO))
  have hpq : IsPullback (fst P.A P.A).left (snd P.A P.A).left P.A.hom P.A.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ P.A, (toUnit P.A ≫ x).left = P.A.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit P.A)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ P.A, cls _ (pull_isLB hF (lift (toUnit P.A ≫ x) (𝟙 P.A)).left) =
      lam (cls P.L P.isLB) (toUnit P.A ≫ x) (𝟙 P.A) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ P.A, cls _ (pull_isLB hF (lift (𝟙 P.A) (toUnit P.A ≫ x)).left) =
      lam (cls P.L P.isLB) (toUnit P.A ≫ x) (𝟙 P.A) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst P.A P.A).left ≫ P.A.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ P.A := Over.homMk x hx
    refine ⟨(lift (toUnit P.A ≫ x') (𝟙 P.A)).left, ?_, ?_, ac_of_primitive P.isAb hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit P.A ≫ x') (𝟙 P.A))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit P.A ≫ x') (𝟙 P.A))
    · rw [s₁, lam_sub, lam_lam P.isLB hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero, lam_const]
      refine fun e => hno ⟨x', (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans ?_)⟩
      refine Eq.trans ?_ (cls_linComb P.isLB _ _ _).symm
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact (congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)).symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ P.A.left := η[P.A].left
  have ho : o ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set P.A.left) := by
    have : IsClosedImmersion (o ≫ P.A.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o P.A.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ P.A := Over.homMk x hx
      refine ⟨(lift (𝟙 P.A) (toUnit P.A ≫ x')).left, ?_, ?_, ac_of_primitive P.isAb hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 P.A) (toUnit P.A ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 P.A) (toUnit P.A ≫ x'))
      · rw [s₂, lam_lam P.isLB hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[P.A] := (eq_one_of_lam_eq_zero P.isLB P.ktriv x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 P.A) (toUnit P.A ≫ η[P.A])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 P.A) (toUnit P.A ≫ η[P.A]))).trans (cst_left η[P.A]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 P.A) (toUnit P.A ≫ η[P.A])))
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : Nonempty P.A.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PrimitiveOverField
