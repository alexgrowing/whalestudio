import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.TorsKer

theorem pow_eq_one_of_points : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n m : ℕ), (n : K) ≠ 0 →
    (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1) →
    ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ^ n = 1 → x ≫ f.hom = 1 → x ^ m = 1 := by
  intro K _ A C f n m hn hpt T x hx hf
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    have : IsUnit (n : K) := isUnit_iff_ne_zero.2 hn
    simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hZf, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let Z := torsion A.X n
  let iZ : Z ⟶ A.X := torsion.ι A.X n
  have hiZ : iZ ^ n = 1 := by
    rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact (pullback.condition (f := mulN A.X n) (g := (η : 𝟙_ (Over (Sp K)) ⟶ A.X))).trans
      (by rw [CategoryTheory.Hom.one_def]; congr 1; exact toUnit_unique _ _)
  let a : Z.left ⟶ C.X.left := (iZ ≫ f.hom).left
  have : IsClosedImmersion (η[C.X]).left :=
    isClosedImmersion_of_comp_eq_id (Y := Sp K) C.X.hom _ (Over.w _)
  let H : Over (Sp K) := Over.mk (pullback.fst a (η[C.X]).left ≫ Z.hom)
  let j : H ⟶ Z := Over.homMk (pullback.fst a (η[C.X]).left) rfl
  have hHf : IsFinite H.hom := by
    haveI := hZf; show IsFinite (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
  have hHe : Etale H.hom := by
    haveI := hZe
    haveI : FormallyUnramified Z.hom := by infer_instance
    haveI : LocallyOfFinitePresentation Z.hom := by infer_instance
    haveI : IsClosedImmersion (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified (pullback.fst a (η[C.X]).left) := inferInstance
    haveI : FormallyUnramified H.hom := by
      show FormallyUnramified (pullback.fst a (η[C.X]).left ≫ Z.hom)
      exact MorphismProperty.comp_mem @FormallyUnramified _ _ ‹_› ‹FormallyUnramified Z.hom›
    haveI : LocallyOfFinitePresentation H.hom := by
      show LocallyOfFinitePresentation (pullback.fst a (η[C.X]).left ≫ Z.hom); infer_instance
    exact Etale.of_formallyUnramified_of_flat _
  have hjf : j ≫ iZ ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    have h1 : (toUnit H).left = H.hom := by simpa using Over.w (toUnit H)
    have h2 : (η[C.X]).left ≫ C.X.hom = 𝟙 _ := by simpa using Over.w (η[C.X])
    have h3 : a ≫ C.X.hom = Z.hom := Over.w (iZ ≫ f.hom)
    have hs : pullback.snd a (η[C.X]).left = (toUnit H).left := by
      rw [h1]
      show pullback.snd a _ = pullback.fst a _ ≫ Z.hom
      rw [← h3, ← Category.assoc, pullback.condition, Category.assoc, h2]
      exact (Category.comp_id _).symm
    rw [CategoryTheory.Hom.one_def]
    show pullback.fst a _ ≫ a = (toUnit H).left ≫ (η[C.X]).left
    rw [← hs]
    exact pullback.condition
  have hsep : IsSeparated A.X.hom := by
    have := A.ab.proper; infer_instance
  have key : (j ≫ iZ) ^ m = 1 := by
    refine GlobalTheory.GenTorsMap.hom_ext_points hHf hHe hsep _ _ fun y => ?_
    rw [MonObj.comp_one, MonObj.comp_pow]
    refine hpt (y ≫ j ≫ iZ) ?_ ?_
    · rw [← MonObj.comp_pow, ← MonObj.comp_pow, hiZ, MonObj.comp_one, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, hjf, MonObj.comp_one]
  have hx1 : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by
    rw [GlobalTheory.GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
  let x₁ : T ⟶ Z := pullback.lift x (toUnit T) hx1
  have hx₁ : x₁ ≫ iZ = x := pullback.lift_fst _ _ _
  have hw : x₁.left ≫ a = T.hom ≫ (η[C.X]).left := by
    have e := congrArg (fun g => g.left) hf
    simp only [CategoryTheory.Hom.one_def, Over.comp_left] at e
    have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
    rw [← hT, ← e, ← hx₁]
    simp [a]
  let x₂ : T ⟶ H := Over.homMk (pullback.lift x₁.left T.hom hw)
    (by show _ ≫ pullback.fst a _ ≫ Z.hom = _; rw [← Category.assoc, pullback.lift_fst]; exact Over.w x₁)
  have hx₂ : x₂ ≫ j ≫ iZ = x := by
    rw [← hx₁, ← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp [x₂, j]
    exact pullback.lift_fst _ _ _
  rw [← hx₂, ← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.AV.TorsKer
