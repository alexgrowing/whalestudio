import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVRStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpavStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverValuationRing
open GlobalTheory.CechPic

theorem pull_eq_zero_of_mem {Y Z : Scheme.{0}} (W : Y.Opens) (r : Z ⟶ Y) (hr : ∀ z, r z ∈ W) {c : CechPic.Pic Y}
    (h : CechPic.pull W.ι c = 0) : CechPic.pull r c = 0 := by
  have e := IsOpenImmersion.lift_fac W.ι r (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hr z)
  rw [← e, pull_comp, h, map_zero]

theorem cls_pair {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : Y ⟶ X)
    (h : (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]).IsLB) :
    cls _ h = CechPic.pull a (cls L hL) - CechPic.pull b (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem triv_iff (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ B).left) :
    Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull r) ↔
      CechPic.pull r (CechPic.pull ((fst T B ≫ x) * snd T B).left (cls L hL) - CechPic.pull (snd T B).left (cls L hL) -
        CechPic.pull (snd T B).left (cls O hO)) = 0 := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  refine (cls_eq_zero_iff (pull_isLB hM r)).symm.trans ?_
  rw [cls_pull hM, cls_div h₁ h₂, cls_pull hO]
  exact Iff.of_eq (congrArg (fun q => CechPic.pull r (q - _) = 0) (cls_pair hL _ _ h₁))

theorem inK_mul_inv (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    InK B L (x * y⁻¹) := by
  intro p
  obtain ⟨U, hU, h₁⟩ := hx p
  obtain ⟨U', hU', h₂⟩ := hy p
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, ?_⟩
  have hD : (translDiff B L (x * y⁻¹)).IsLB := LB.isLB_linComb hL _ _
  let τ : T ⊗ B ⟶ T ⊗ B := lift (fst T B) ((fst T B ≫ y⁻¹) * snd T B)
  have k₁ : τ ≫ fst T B = fst T B := lift_fst _ _
  have k₂ : ∀ z : T ⟶ B, τ ≫ ((fst T B ≫ z) * snd T B) = (fst T B ≫ (z * y⁻¹)) * snd T B := fun z => by
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, k₁, MonObj.comp_mul, _root_.mul_assoc]
  have m : ∀ z, (fst T B).left ((((fst T B).left ⁻¹ᵁ (U ⊓ U')).ι ≫ τ.left) z) ∈ U ⊓ U' := fun z => by
    have e := congrArg (fun q : T ⊗ B ⟶ T => q.left z.1) k₁
    exact (congrArg (· ∈ U ⊓ U') e).mpr z.2
  have a₁ := pull_eq_zero_of_mem _ _ (fun z => (m z).1) ((triv_iff hL hO x _).1 h₁)
  have a₂ := pull_eq_zero_of_mem _ _ (fun z => (m z).2) ((triv_iff hL hO y _).1 h₂)
  have a := congrArg₂ (· - ·) a₁ a₂
  simp only [← map_sub, sub_sub_sub_cancel_right, sub_zero] at a
  rw [pull_comp, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₂, k₂, mul_inv_cancel,
    MonObj.comp_one, _root_.one_mul] at a
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  exact (congrArg _ (cls_pair hL _ _ hD)).trans a

end Points

theorem exists_geometric_point (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {O : LB P.A.left} (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) :
    ∃ x : Over.mk f ⟶ P.A, Triv (LB.div (translDiff P.A P.L x) (O.pull (snd (Over.mk f) P.A).left)) := by
  obtain ⟨P', g, hg, -, hm, ht⟩ := hL.polBaseChange S _ f P
  have hc : CechPic.pull g (cls P.L P.isLB) = cls P'.L P'.isLB := (cls_eq_iff (pull_isLB P.isLB g) P'.isLB).2 ht
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ P'.A) = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst P.A P.A) (snd P.A P.A) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst P'.A P'.A) (snd P'.A P'.A) = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst P'.A P'.A)) (toBase hg.w (snd P'.A P'.A))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_primitiveBundle_eq_translate_ppav hL K P' (O.pull g) hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb P'.isLB _ _)).2 hx').trans (cls_pair P'.isLB _ _ _)
  let T : Over S := Over.mk f
  have wx : x'.left ≫ P'.A.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ P.A.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T P.A).left ≫ P.A.hom = (fst T P.A).left ≫ f := (Over.w (snd T P.A)).trans (Over.w (fst T P.A)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ P.A).left) (fst T P.A).left
  let h : T' ⟶ P'.A := Over.homMk (hg.lift (snd T P.A).left (fst T P.A).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T P.A).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ P.A := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T P.A)).symm)
  have b₁ : u ≫ snd T P.A = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T P.A ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T P.A).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T P.A).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A).left ≫ g = ((fst T P.A ≫ x) * snd T P.A).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A)) = u ≫ ((fst T P.A ≫ x) * snd T P.A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff P.A P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have h₂ := pull_isLB hO (snd T P.A).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair P.isLB _ _ h₁).trans e'.symm

theorem isIso_of_flat_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] [_root_.IsReduced V] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of V)) [IsClosedImmersion q] [Flat q] (h : X) (hh : q h = IsLocalRing.closedPoint V) :
    IsIso q := by
  have : Surjective q := ⟨fun s => by
    obtain ⟨y, -, hy⟩ := Flat.generalizingMap q (a := h) (b := s) (by
      rw [hh]; exact IsLocalRing.specializes_closedPoint s)
    exact ⟨y, hy⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective q

theorem exists_section_translate : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P : PolAV (Spec (CommRingCat.of V))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have flat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hL.globalFns V P.A P.isAb proj ⟨P.L, r, P.isLB, hr⟩ c O hO hu H j hj hH fin
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  have : IsIso H.hom := isIso_of_flat_of_closedPoint H.hom (y.left (IsLocalRing.closedPoint K))
    ((congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ))
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H := Over.homMk (inv H.hom) (IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverValuationRing
