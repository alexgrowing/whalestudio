import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.LevelStructureForms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NatCardEqOfEquivPiField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsOfCubeBundleGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCompare

theorem rel_of_basis {G U J : Type} [CommGroup G] [CommGroup U] [Fintype J] [DecidableEq J]
    (W : G → G → U → Prop) (φ : (J → ℤ) → G) (hφ : ∀ a b, φ (a + b) = φ a * φ b)
    (ex : ∀ a b, ∃! c, W (φ a) (φ b) c)
    (mul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (skew : ∀ x y c, W x y c → W y x c⁻¹)
    (β : (J → ℤ) → (J → ℤ) → ℤ) (β₁ : ∀ a a' b, β (a + a') b = β a b + β a' b)
    (β₂ : ∀ a b b', β a (b + b') = β a b + β a b') (ζ : U)
    (h : ∀ i j, W (φ (Pi.single i 1)) (φ (Pi.single j 1)) (ζ ^ β (Pi.single i 1) (Pi.single j 1)))
    (a b : J → ℤ) : W (φ a) (φ b) (ζ ^ β a b) := by
  choose e he hu using ex
  have e₁ : ∀ a a' b, e (a + a') b = e a b * e a' b := fun a a' b =>
    (hu _ _ _ (by rw [hφ]; exact mul _ _ _ _ _ (he a b) (he a' b))).symm
  have es : ∀ a b, e b a = (e a b)⁻¹ := fun a b => (hu _ _ _ (skew _ _ _ (he a b))).symm
  have e₂ : ∀ a b b', e a (b + b') = e a b * e a b' := fun a b b' => by
    rw [es, e₁, mul_inv, ← es, ← es]
  let E : (J → ℤ) →+ (J → ℤ) →+ Additive U :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => Additive.ofMul (e a b))
      (fun b b' => congrArg Additive.ofMul (e₂ a b b')))
      (fun a a' => AddMonoidHom.ext fun b => congrArg Additive.ofMul (e₁ a a' b))
  let F : (J → ℤ) →+ (J → ℤ) →+ Additive U :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => Additive.ofMul (ζ ^ β a b))
      (fun b b' => by rw [β₂, zpow_add]; rfl))
      (fun a a' => AddMonoidHom.ext fun b => by
        show Additive.ofMul (ζ ^ β (a + a') b) = _
        rw [β₁, zpow_add]; rfl)
  have hEF : E = F := AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int <|
    AddMonoidHom.functions_ext' _ _ _ fun j => AddMonoidHom.ext_int <|
      congrArg Additive.ofMul (hu _ _ _ (h i j)).symm
  have : e a b = ζ ^ β a b := congrArg (fun H : (J → ℤ) →+ (J → ℤ) →+ Additive U => (H a b).toMul) hEF
  exact this ▸ he a b

variable {S : Scheme.{0}}

theorem eq_section_of_range {X T : Over S} (t : 𝟙_ (Over S) ⟶ X) [IsOpenImmersion t.left]
    (u : T ⟶ X) (h : Set.range u.left ⊆ Set.range t.left) : toUnit T ≫ t = u := by
  have hl := IsOpenImmersion.lift_fac t.left u.left h
  have e : t.left ≫ X.hom = 𝟙 S := Over.w t
  let l : T ⟶ 𝟙_ (Over S) := Over.homMk (IsOpenImmersion.lift t.left u.left h) (by
    change _ ≫ 𝟙 S = T.hom
    rw [← Over.w u, ← e]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.hom) hl))
  rw [toUnit_unique (toUnit _) l]
  exact Over.OverMorphism.ext hl

theorem exists_geomPoint (X : Over S) (x : X.left) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Spec (CommRingCat.of K) ⟶ S)
      (u : Over.mk s ⟶ X), Set.range u.left = {x} := by
  let K := AlgebraicClosure (X.left.residueField x)
  let u : Spec (CommRingCat.of K) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.residueField x) K)) ≫
      X.left.fromSpecResidueField x
  refine ⟨K, inferInstance, inferInstance, u ≫ X.hom, Over.homMk u rfl, ?_⟩
  have hu : ∀ p, u p = x := fun p =>
    (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply x _)
  ext z
  exact ⟨fun ⟨p, hp⟩ => hp.symm.trans (hu p), fun hz => ⟨(⊥ : PrimeSpectrum K), (hu _).trans hz.symm⟩⟩

def ListsGeomPoints {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) (u : Over.mk s ⟶ X),
    ∃! i, toUnit _ ≫ t i = u

theorem isIso_desc_iff {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X)) :
    IsIso (Sigma.desc t) ↔ IsIso (Sigma.desc (f := fun _ : I => S) fun i => (t i).left) := by
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X t)).symm.trans (Iff.trans ?_
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk (f := fun _ : I => S) X.left fun i => (t i).left)))
  constructor
  · rintro ⟨h⟩
    exact ⟨isColimitMapCoconeCofanMkEquiv (Over.forget S) _ t (isColimitOfPreserves (Over.forget S) h)⟩
  · rintro ⟨h⟩
    exact ⟨isColimitOfReflects (Over.forget S)
      ((isColimitMapCoconeCofanMkEquiv (Over.forget S) _ t).symm h)⟩

theorem isIso_desc_of_lists {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X))
    [FormallyUnramified X.hom] [LocallyOfFiniteType X.hom] (h : ListsGeomPoints t) :
    IsIso (Sigma.desc t) := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have ho : ∀ i, IsOpenImmersion (t i).left := fun i =>
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) (t i).left X.hom
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal X.hom)))
      (by rw [Over.w (t i)]; exact inferInstanceAs (IsOpenImmersion (𝟙 S)))
  rw [isIso_desc_iff]
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk (f := fun _ : I => S) X.left fun i => (t i).left)).1
    (@nonempty_isColimit_cofanMk_of _ _ (fun _ : I => S) _ (fun i => (t i).left) ho ?_ ?_)
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨K, _, _, s, u, hu⟩ := exists_geomPoint X x
    obtain ⟨i, hi, -⟩ := h K s u
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    obtain ⟨p, hp⟩ : x ∈ Set.range u.left := hu ▸ rfl
    rw [← hi, Over.comp_left, Scheme.Hom.comp_apply] at hp
    exact ⟨_, hp⟩
  · intro i j hij U hi hj x hx
    obtain ⟨K, _, _, s, u, hu⟩ := exists_geomPoint X x
    exact (hij ((h K s u).unique
      (eq_section_of_range (t i) u (hu ▸ Set.singleton_subset_iff.2 (hi hx)))
      (eq_section_of_range (t j) u (hu ▸ Set.singleton_subset_iff.2 (hj hx))))).elim

theorem lists_of_isIso_desc {I : Type} {X : Over S} (t : I → (𝟙_ (Over S) ⟶ X))
    (h : IsIso (Sigma.desc t)) : ListsGeomPoints t ∧ FormallyUnramified X.hom := by
  rw [isIso_desc_iff] at h
  set e := Sigma.desc (f := fun _ : I => S) fun i => (t i).left with he
  have ht : ∀ i, (t i).left = Sigma.ι (fun _ : I => S) i ≫ e := fun i =>
    (Sigma.ι_desc (f := fun _ : I => S) (fun i => (t i).left) i).symm
  have ho : ∀ i, IsOpenImmersion (t i).left := fun i => by
    rw [ht]; exact IsOpenImmersion.comp _ _
  refine ⟨fun K _ _ s u => ?_, ?_⟩
  · let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    obtain ⟨z, hz⟩ := e.surjective (u.left p)
    obtain ⟨i, y, hy⟩ : ∃ (c : I) (y : S), Sigma.ι (fun _ : I => S) c y = z :=
      (sigmaOpenCover fun _ : I ↦ S).exists_eq z
    refine existsUnique_of_exists_of_unique ⟨i, eq_section_of_range (t i) u ?_⟩ fun i j hi hj => ?_
    · rintro _ ⟨q, rfl⟩
      obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum K) _ _
      exact ⟨y, by rw [ht, ← hz, ← hy]; exact Scheme.Hom.comp_apply _ _ _⟩
    · have h₁ : (toUnit (Over.mk s)).left ≫ (t i).left = (toUnit (Over.mk s)).left ≫ (t j).left :=
        congrArg CommaMorphism.left (hi.trans hj.symm)
      rw [ht, ht] at h₁
      have h₂ : (toUnit (Over.mk s)).left ≫ Sigma.ι (fun _ : I => S) i =
          (toUnit (Over.mk s)).left ≫ Sigma.ι (fun _ : I => S) j := by
        rw [← cancel_mono e]
        exact (Category.assoc _ _ _).trans (h₁.trans (Category.assoc _ _ _).symm)
      by_contra hij
      exact (isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => S) ⟨h₂⟩ hij).elim p
  · suffices H : FormallyUnramified (e ≫ X.hom) by
      rw [← IsIso.inv_hom_id_assoc e X.hom]
      exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance H
    haveI : IsZariskiLocalAtSource @FormallyUnramified.{0} :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FormallyUnramified)
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified.{0})
        (sigmaOpenCover fun _ : I => S)]
    intro (i : I)
    have : Sigma.ι (fun _ : I => S) i ≫ e ≫ X.hom = 𝟙 S := by
      rw [← Category.assoc, ← ht]; exact Over.w (t i)
    exact (this.symm ▸ inferInstance : FormallyUnramified (Sigma.ι (fun _ : I => S) i ≫ e ≫ X.hom))

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms (mulBy constOver stdForm reduce)

abbrev Ker (A : Over S) [GrpObj A] (k : ℕ) : Over S := pullback (mulBy A k) η[A]

theorem comp_mulBy {A T : Over S} [GrpObj A] (x : T ⟶ A) (k : ℕ) : x ≫ mulBy A k = x ^ k := by
  rw [mulBy, MonObj.comp_pow, Category.comp_id]

def kerPt {A T : Over S} [GrpObj A] {k : ℕ} (x : T ⟶ A) (hx : x ^ k = 1) : T ⟶ Ker A k :=
  pullback.lift x (toUnit _) (by rw [comp_mulBy, hx, Hom.one_def])

theorem kerPt_fst {A T : Over S} [GrpObj A] {k : ℕ} (x : T ⟶ A) (hx : x ^ k = 1) :
    kerPt x hx ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _

theorem ker_ext {A T : Over S} [GrpObj A] {k : ℕ} {u v : T ⟶ Ker A k}
    (h : u ≫ pullback.fst _ _ = v ≫ pullback.fst _ _) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

theorem isKer_iff {A : Over S} [GrpObj A] {k : ℕ} {I : Type} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ i, x i ^ k = 1) :
    IsPullback (Sigma.desc x : constOver S I ⟶ A) (toUnit _) (mulBy A k) η[A] ↔
      IsIso (Sigma.desc fun i => kerPt (x i) (hx i)) := by
  have e : (Sigma.desc fun i => kerPt (x i) (hx i)) ≫ pullback.fst _ _ = Sigma.desc x :=
    Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc_assoc, kerPt_fst, Sigma.ι_desc]
  constructor
  · intro h
    rw [show (Sigma.desc fun i => kerPt (x i) (hx i)) = h.isoPullback.hom from
      ker_ext (e.trans h.isoPullback_hom_fst.symm)]
    infer_instance
  · intro h
    exact (IsPullback.of_hasPullback (mulBy A k) η[A]).of_iso'
      (asIso (Sigma.desc fun i => kerPt (x i) (hx i))) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using e) (toUnit_unique _ _) (by simp) (by simp)

theorem lists_kerPt_iff {A : Over S} [GrpObj A] {k : ℕ} {I : Type} (x : I → (𝟙_ (Over S) ⟶ A))
    (hx : ∀ i, x i ^ k = 1) :
    ListsGeomPoints (fun i => kerPt (x i) (hx i)) ↔
      ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) (y : Over.mk s ⟶ A),
        y ^ k = 1 → ∃! i, toUnit _ ≫ x i = y := by
  have key : ∀ {T : Over S} (u : T ⟶ Ker A k) i,
      toUnit _ ≫ kerPt (x i) (hx i) = u ↔ toUnit _ ≫ x i = u ≫ pullback.fst _ _ := fun u i =>
    ⟨fun h => by rw [← h, Category.assoc, kerPt_fst],
      fun h => ker_ext (by rw [← h, Category.assoc, kerPt_fst])⟩
  constructor
  · intro h K _ _ s y hy
    have := h K s (kerPt y hy)
    simpa only [key, kerPt_fst] using this
  · intro h K _ _ s u
    simp only [key]
    refine h K s _ ?_
    rw [← comp_mulBy, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _

theorem locallyOfFiniteType_ker (A : Over S) [GrpObj A] [LocallyOfFiniteType A.hom] (k : ℕ) :
    LocallyOfFiniteType (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (mulBy A k) η[A]).map (Over.forget S)
  have : LocallyOfFiniteType (η[A].left ≫ A.hom) := by
    rw [Over.w η[A]]; exact inferInstanceAs (LocallyOfFiniteType (𝟙 S))
  have h₁ : LocallyOfFiniteType η[A].left := locallyOfFiniteType_of_comp _ A.hom
  have h₂ : LocallyOfFiniteType (pullback.fst (mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h.flip h₁
  rw [← Over.w (pullback.fst (mulBy A k) η[A])]
  infer_instance

theorem formallyUnramified_ker (A : Over S) [GrpObj A] [IsCommMonObj A] {k : ℕ}
    (hk : IsUnit (k : Γ(S, ⊤))) : FormallyUnramified (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (mulBy A k) η[A]).map (Over.forget S)
  have h₁ : FormallyUnramified (mulBy A k).left := GlobalTheory.formallyUnramified_mulA S A k hk
  have h₂ : FormallyUnramified (pullback.snd (mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @FormallyUnramified) h h₁
  rw [← Over.w (pullback.snd (mulBy A k) η[A])]
  exact MorphismProperty.comp_mem @FormallyUnramified _ _ h₂
    (inferInstanceAs (FormallyUnramified (𝟙 S)))

theorem weil_existsUnique (P : PolAV S) (k : ℕ) {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1)
    (hy : y ^ k = 1) : ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c :=
  GlobalTheory.CommutatorPairing.existsUnique_weilIs GlobalTheory.laws_without_cohomology.1
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1).2.2
    S P k T x y hx hy

theorem weil_skew_natural (P : PolAV S) (k : ℕ) (T : Over S) :
    (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧
    ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c →
      WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) :=
  (GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1
    (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1).2.2
    S P k T).2

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) :=
  finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem stdForm_single (g : ℕ) (i j : Fin g ⊕ Fin g) :
    stdForm (Pi.single i 1) (Pi.single j 1) = stdSymp g (halves g i) (halves g j) := by
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2 <;>
    simp only [stdSymp, halves_inl, halves_inr] <;>
    simp [stdForm, Pi.single_apply] <;> split_ifs <;> omega

theorem stdForm_add_left {g : ℕ} (a a' b : Fin g ⊕ Fin g → ℤ) :
    stdForm (a + a') b = stdForm a b + stdForm a' b := by
  simp only [stdForm, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem stdForm_add_right {g : ℕ} (a b b' : Fin g ⊕ Fin g → ℤ) :
    stdForm a (b + b') = stdForm a b + stdForm a b' := by
  simp only [stdForm, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem reduce_add {g : ℕ} (k : ℕ) (a b : Fin g ⊕ Fin g → ℤ) :
    reduce k (a + b) = reduce k a + reduce k b := funext fun j => by simp [reduce]

theorem reduce_single {g : ℕ} (k : ℕ) (i : Fin g ⊕ Fin g) (n : ℤ) :
    reduce k (Pi.single i n) = Pi.single i (n : ZMod k) := funext fun j => by
  simp only [reduce, Pi.single_apply]
  split_ifs <;> simp

def basisHom {G J : Type} [CommGroup G] [Fintype J] {k : ℕ} [NeZero k] (y : J → G)
    (hy : ∀ i, y i ^ k = 1) : Multiplicative (J → ZMod k) →* G :=
  MonoidHom.mk' (fun a => ∏ i, y i ^ (a.toAdd i).val) fun a b => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hy i), pow_add]

theorem basisHom_single {G J : Type} [CommGroup G] [Fintype J] [DecidableEq J] {k : ℕ} [NeZero k]
    (y : J → G) (hy : ∀ i, y i ^ k = 1) (i : J) :
    basisHom y hy (Multiplicative.ofAdd (Pi.single i 1)) = y i := by
  change ∏ j, y j ^ ((Pi.single i (1 : ZMod k) : J → ZMod k) j).val = y i
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp),
    Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hy i), pow_one]

theorem hom_pow {G J : Type} [Monoid G] {k : ℕ} (φ : Multiplicative (J → ZMod k) →* G)
    (a : Multiplicative (J → ZMod k)) : φ a ^ k = 1 := by
  rw [← map_pow, ← map_one φ]
  congr 1
  exact funext fun i => by
    change (k • a.toAdd) i = 0
    simp

theorem hom_eq_basisHom {G J : Type} [CommGroup G] [Fintype J] [DecidableEq J] {k : ℕ} [NeZero k]
    (φ : Multiplicative (J → ZMod k) →* G) :
    basisHom (fun i => φ (Multiplicative.ofAdd (Pi.single i 1))) (fun _ => hom_pow φ _) = φ := by
  refine MonoidHom.ext fun a => ?_
  change ∏ i, φ (Multiplicative.ofAdd (Pi.single i 1)) ^ (a.toAdd i).val = φ a
  simp only [← map_pow, ← map_prod, ← ofAdd_nsmul, ← ofAdd_sum]
  refine congrArg φ ((congrArg Multiplicative.ofAdd (funext fun j => ?_)).trans (ofAdd_toAdd a))
  simp [Finset.sum_apply, Pi.single_apply, ZMod.natCast_zmod_val, -ZMod.natCast_val]

theorem comp_basisHom {A T : Over S} [GrpObj A] [IsCommMonObj A] {g k : ℕ} [NeZero k]
    (y : Fin (2 * g) → (𝟙_ (Over S) ⟶ A)) (hy : ∀ i, y (halves g i) ^ k = 1)
    (h : T ⟶ 𝟙_ (Over S)) (a : Fin g ⊕ Fin g → ZMod k) :
    h ≫ basisHom (fun i => y (halves g i)) hy (Multiplicative.ofAdd a) =
      linComb (fun i => h ≫ y i) (fun i => (a ((halves g).symm i)).val) := by
  let F : (𝟙_ (Over S) ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (h ≫ ·) fun a b => MonObj.comp_mul _ _ _
  rw [linComb, List.prod_ofFn, ← (halves g).prod_comp]
  refine (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [Equiv.symm_apply_apply]
  exact map_pow F _ _

def coeff (g k : ℕ) [NeZero k] : (Fin g ⊕ Fin g → ZMod k) ≃ (Fin (2 * g) → Fin k) where
  toFun a i := ⟨(a ((halves g).symm i)).val, ZMod.val_lt _⟩
  invFun c j := ((c (halves g j) : ℕ) : ZMod k)
  left_inv a := funext fun j => by simp
  right_inv c := funext fun i => Fin.ext (by simp [ZMod.val_cast_of_lt (c i).2])

theorem indep_span_iff {A T : Over S} [GrpObj A] [IsCommMonObj A] {g k : ℕ} [NeZero k]
    (y : Fin (2 * g) → (𝟙_ (Over S) ⟶ A)) (hy : ∀ i, y (halves g i) ^ k = 1)
    (h : T ⟶ 𝟙_ (Over S)) :
    ((∀ c c' : Fin (2 * g) → Fin k, linComb (fun i => h ≫ y i) (fun i => (c i : ℕ)) =
        linComb (fun i => h ≫ y i) (fun i => (c' i : ℕ)) → c = c') ∧
      ∀ z : T ⟶ A, z ^ k = 1 →
        ∃ c : Fin (2 * g) → Fin k, linComb (fun i => h ≫ y i) (fun i => (c i : ℕ)) = z) ↔
    ∀ z : T ⟶ A, z ^ k = 1 →
      ∃! a, toUnit T ≫ basisHom (fun i => y (halves g i)) hy (Multiplicative.ofAdd a) = z := by
  have e : ∀ a, toUnit T ≫ basisHom (fun i => y (halves g i)) hy (Multiplicative.ofAdd a) =
      linComb (fun i => h ≫ y i) (fun i => (coeff g k a i : ℕ)) := fun a => by
    rw [toUnit_unique (toUnit T) h]; exact comp_basisHom y hy h a
  constructor
  · rintro ⟨h₁, h₂⟩ z hz
    obtain ⟨c, hc⟩ := h₂ z hz
    obtain ⟨a, rfl⟩ := (coeff g k).surjective c
    exact ⟨a, (e a).trans hc, fun b hb =>
      (coeff g k).injective (h₁ _ _ (((e b).symm.trans hb).trans hc.symm))⟩
  · refine fun H => ⟨fun c c' hc => ?_, fun z hz => ?_⟩
    · obtain ⟨a, rfl⟩ := (coeff g k).surjective c
      obtain ⟨a', rfl⟩ := (coeff g k).surjective c'
      rw [← e, ← e] at hc
      exact congrArg _ ((H _ (by rw [← MonObj.comp_pow, hom_pow, MonObj.comp_one])).unique hc rfl)
    · obtain ⟨a, ha, -⟩ := H z hz
      exact ⟨_, (e a).symm.trans ha⟩

variable {P : PolAV S} {k : ℕ} {ζ : Γ(S, ⊤)ˣ}

local instance isComm (P : PolAV S) : IsCommMonObj P.A := P.isAb.comm

theorem torsion_halves (lev : Out.Level P k ζ) (i : Fin P.g ⊕ Fin P.g) :
    (lev.pt (halves P.g i) : 𝟙_ (Over S) ⟶ P.A) ^ k = 1 := lev.torsion _

def homOfBasis [NeZero k] (lev : Out.Level P k ζ) :
    Multiplicative (Fin P.g ⊕ Fin P.g → ZMod k) →* (𝟙_ (Over S) ⟶ P.A) :=
  basisHom (fun i => lev.pt (halves P.g i)) (torsion_halves lev)

theorem homOfBasis_single [NeZero k] (lev : Out.Level P k ζ) (i : Fin P.g ⊕ Fin P.g) :
    homOfBasis lev (Multiplicative.ofAdd (Pi.single i 1)) = lev.pt (halves P.g i) :=
  basisHom_single _ _ i

theorem pairing_of_basis [NeZero k] (lev : Out.Level P k ζ) (a b : Fin P.g ⊕ Fin P.g → ℤ) :
    WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S))
      (homOfBasis lev (Multiplicative.ofAdd (reduce k a)))
      (homOfBasis lev (Multiplicative.ofAdd (reduce k b))) (ζ ^ stdForm a b : Γ(S, ⊤)ˣ) := by
  refine rel_of_basis (U := Γ(S, ⊤)ˣ) (fun x y c => WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S)) x y c)
    (fun a => homOfBasis lev (Multiplicative.ofAdd (reduce k a)))
    (fun a b => by rw [reduce_add, ofAdd_add, map_mul])
    (fun a b => weil_existsUnique P k (T := 𝟙_ (Over S)) _ _ (hom_pow (homOfBasis lev) _)
      (hom_pow (homOfBasis lev) _))
    (GlobalTheory.weilIs_mul_left GlobalTheory.laws_without_cohomology.1 S P k _) (weil_skew_natural P k _).1
    stdForm stdForm_add_left stdForm_add_right ζ (fun i j => ?_) a b
  simp only [reduce_single, Int.cast_one, homOfBasis_single, stdForm_single]
  exact lev.pairing _ _

def toIso [NeZero k] (hU : FormallyUnramified (Ker P.A k).hom) (lev : Out.Level P k ζ) :
    IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ where
  hom := homOfBasis lev
  isKer := by
    have := P.isAb.smooth
    have := locallyOfFiniteType_ker P.A k
    refine (isKer_iff _ fun a => hom_pow _ _).2 (isIso_desc_of_lists _
      ((lists_kerPt_iff _ _).2 fun K _ _ s => ?_))
    exact (indep_span_iff (A := P.A) lev.pt (torsion_halves lev) _).1 ⟨lev.indep K s, lev.span K s⟩
  pairing := pairing_of_basis lev

theorem lists_of_iso (ℓ : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ) (K : Type) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (y : Over.mk s ⟶ P.A) (hy : y ^ k = 1) :
    ∃! a, toUnit _ ≫ ℓ.pt a = y :=
  (lists_kerPt_iff _ fun _ => hom_pow ℓ.hom _).1
    (lists_of_isIso_desc _ ((isKer_iff _ _).1 ℓ.isKer)).1 K s y hy

theorem unramified_of_iso (ℓ : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ) : FormallyUnramified (Ker P.A k).hom :=
  (lists_of_isIso_desc _ ((isKer_iff _ fun _ => hom_pow ℓ.hom _).1 ℓ.isKer)).2

theorem indep_span_of_iso [NeZero k] (ℓ : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ) (K : Type) [Field K]
    [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) (h : Over.mk s ⟶ 𝟙_ (Over S)) :
    (∀ c c' : Fin (2 * P.g) → Fin k,
      linComb (fun i => h ≫ ℓ.pt (Pi.single ((halves P.g).symm i) 1)) (fun i => (c i : ℕ)) =
        linComb (fun i => h ≫ ℓ.pt (Pi.single ((halves P.g).symm i) 1)) (fun i => (c' i : ℕ)) →
          c = c') ∧
      ∀ z : Over.mk s ⟶ P.A, z ^ k = 1 → ∃ c : Fin (2 * P.g) → Fin k,
        linComb (fun i => h ≫ ℓ.pt (Pi.single ((halves P.g).symm i) 1)) (fun i => (c i : ℕ)) = z := by
  refine (indep_span_iff (fun i => ℓ.pt (Pi.single ((halves P.g).symm i) 1))
    (fun _ => hom_pow ℓ.hom _) h).2 fun z hz => ?_
  simp only [Equiv.symm_apply_apply, IndefiniteRowSideFullHecke.LevelStructureForms.Level.pt, hom_eq_basisHom]
  exact lists_of_iso ℓ K s z hz

def ofIso [NeZero k] (hζ : IsPrimitiveRoot ζ k) (ℓ : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ) :
    Out.Level P k ζ where
  pt i := ℓ.pt (Pi.single ((halves P.g).symm i) 1)
  prim := hζ
  torsion _ := hom_pow ℓ.hom _
  indep K _ _ s := (indep_span_of_iso ℓ K s _).1
  span K _ _ s := (indep_span_of_iso ℓ K s _).2
  pairing i j := by
    have h := ℓ.pairing (Pi.single ((halves P.g).symm i) 1) (Pi.single ((halves P.g).symm j) 1)
    simp only [reduce_single, Int.cast_one, stdForm_single, Equiv.apply_symm_apply] at h
    exact h

theorem basis_ext {l l' : Out.Level P k ζ} (h : l.pt = l'.pt) : l = l' := by
  cases l; cases l'; cases h; rfl

theorem iso_ext {l l' : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ} (h : l.hom = l'.hom) : l = l' := by
  cases l; cases l'; cases h; rfl

def equivExact (P : PolAV S) (k : ℕ) [NeZero k] (ζ : Γ(S, ⊤)ˣ) :
    {_l : Out.Level P k ζ // FormallyUnramified (Ker P.A k).hom} ≃
      {_l : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ // IsPrimitiveRoot ζ k} where
  toFun l := ⟨toIso l.2 l.1, l.1.prim⟩
  invFun l := ⟨ofIso l.2 l.1, unramified_of_iso l.1⟩
  left_inv l := Subtype.ext (basis_ext (funext fun i =>
    (homOfBasis_single l.1 _).trans (by rw [Equiv.apply_symm_apply])))
  right_inv l := Subtype.ext (iso_ext (by
    change basisHom (fun i => l.1.pt (Pi.single ((halves P.g).symm (halves P.g i)) 1))
      (fun _ => hom_pow l.1.hom _) = _
    simp only [Equiv.symm_apply_apply, IndefiniteRowSideFullHecke.LevelStructureForms.Level.pt, hom_eq_basisHom]))

theorem neZero_of_prim (hk : IsUnit (k : Γ(S, ⊤))) (hζ : IsPrimitiveRoot ζ k) : NeZero k := ⟨by
  rintro rfl
  rw [Nat.cast_zero, isUnit_zero_iff] at hk
  have := subsingleton_of_zero_eq_one hk
  exact one_ne_zero (zero_dvd_iff.1 (hζ.dvd_of_pow_eq_one 1 (Subsingleton.elim _ _)))⟩

def equivOfUnit (P : PolAV S) (hk : IsUnit (k : Γ(S, ⊤))) (hζ : IsPrimitiveRoot ζ k) :
    Out.Level P k ζ ≃ IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ :=
  haveI := neZero_of_prim hk hζ
  ((Equiv.subtypeUnivEquiv fun _ => formallyUnramified_ker P.A hk).symm.trans
    (equivExact P k ζ)).trans (Equiv.subtypeUnivEquiv fun _ => hζ)

def changeRoot (hg : P.g = 0) (ℓ : IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ) (ζ' : Γ(S, ⊤)ˣ) :
    IndefiniteRowSideFullHecke.LevelStructureForms.Level P k ζ' where
  hom := ℓ.hom
  isKer := ℓ.isKer
  pairing a b := by
    have h := ℓ.pairing a b
    have : IsEmpty (Fin P.g) := hg ▸ inferInstanceAs (IsEmpty (Fin 0))
    rw [show stdForm a b = 0 from Finset.sum_of_isEmpty _, zpow_zero] at h ⊢
    exact h

end GlobalTheory.LevelCompare
