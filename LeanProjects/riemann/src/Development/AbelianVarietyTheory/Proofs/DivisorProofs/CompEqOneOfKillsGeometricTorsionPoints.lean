import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem comp_hom_eq_one_of_torsion_pts (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ)
    (hn : (n : K) ≠ 0) (hker : ∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1)
    (T : Over (Sp K)) (x : T ⟶ A.X) (hx : x ^ n = 1) : x ≫ f.hom = 1 := by
  have hA := A.ab
  have hC := C.ab
  have := hA.proper
  have := hC.proper
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨_, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion A.X hu
  have hι : torsion.ι A.X n ≫ mulN A.X n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))
  set L := AlgebraicClosure K
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let P := (Over.pullback t).obj (torsion A.X n)
  let C' := (Over.pullback t).obj C.X
  have hP : Etale P.hom := by
    change Etale (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hPf : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hC' : IsProper C'.hom := by
    change IsProper (pullback.snd C.X.hom t)
    infer_instance
  have hPr : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  have hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t =
      pullback.fst (torsion A.X n).hom t ≫ g.left := fun g => by
    simp
    exact pullback.lift_fst _ _ _
  have hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) =
      (Over.pullback t).map (1 : torsion A.X n ⟶ C.X) := by
    refine TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_
    let z : Sp L ⟶ (torsion A.X n).left := y.left ≫ pullback.fst (torsion A.X n).hom t
    have hz : z ≫ (torsion A.X n).hom = t := by
      have e1 : y.left ≫ P.hom = 𝟙 _ := by
        change y.left ≫ pullback.snd (torsion A.X n).hom t = _
        simpa using Over.w y
      simp only [z, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      change (y.left ≫ P.hom) ≫ t = t
      rw [e1, Category.id_comp]
    let z' : ptOver K L ⟶ torsion A.X n := Over.homMk z hz
    have hw : (z' ≫ torsion.ι A.X n) ^ n = 1 := by
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have hk := hker (z' ≫ torsion.ι A.X n) hw
    have hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X) := by
      rw [MonObj.comp_one, ← Category.assoc, hk]
    have hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left :=
      congrArg CommaMorphism.left hk'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, hfst]
      simpa [z] using hkl
    · have w1 := Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))
      have w2 := Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))
      change _ ≫ pullback.snd C.X.hom t = _ at w1 w2
      rw [w1, w2]
  have hred : IsReduced (torsion A.X n).left := isReduced_of_smooth_of_isReduced (torsion A.X n).hom
  have hdom : IsDominant (pullback.fst (torsion A.X n).hom t) := inferInstance
  have h6 : torsion.ι A.X n ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_
    rw [← hfst, ← hfst, hEq]
  have e : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
  obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x :=
    ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
  rw [← e', Category.assoc, h6, MonObj.comp_one]

end GlobalTheory.AV.AbVar

end
