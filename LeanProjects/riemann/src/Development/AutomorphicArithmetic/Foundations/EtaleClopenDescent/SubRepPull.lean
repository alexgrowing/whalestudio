import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace UpperTheory.SubRep

variable {S T : Scheme.{0}} {A : Over S} [GrpObj A] {x : T ⟶ S} {A₁ : Over T} [GrpObj A₁]
  {φ₁ : A₁.left ⟶ A.left}

theorem pull_existsUnique (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) (a : T' ⟶ A) :
    ∃! g : Over.mk t ⟶ A₁, g.left ≫ φ₁ = a.left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨hPb, -⟩ := hP'
  have hw : a.left ≫ A.hom = t ≫ x := by rw [Over.w a, ht]
  refine ⟨Over.homMk (hPb.lift a.left t hw) (hPb.lift_snd _ _ _), hPb.lift_fst _ _ _, ?_⟩
  intro g' hg'
  apply Over.OverMorphism.ext
  apply hPb.hom_ext
  · rw [hg']
    exact (hPb.lift_fst _ _ _).symm
  · exact (Over.w g').trans (hPb.lift_snd _ _ _).symm

theorem pull_ext (hP : IsGrpPullback A₁ A x φ₁) {T' : Over T} {g g' : T' ⟶ A₁}
    (h : g.left ≫ φ₁ = g'.left ≫ φ₁) : g = g' := by
  apply Over.OverMorphism.ext
  apply hP.1.hom_ext h
  rw [Over.w g, Over.w g']

theorem pull_mul (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) {g g' : Over.mk t ⟶ A₁} {a a' : T' ⟶ A}
    (h : g.left ≫ φ₁ = a.left) (h' : g'.left ≫ φ₁ = a'.left) :
    (g * g').left ≫ φ₁ = (a * a').left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨-, hPm⟩ := hP'
  let e : Over.mk (t ≫ x) ⟶ T' := Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact ht.symm)
  have key := hPm (Over.mk t) g g' (e ≫ a) (e ≫ a')
    (by rw [Over.comp_left, ← h]; exact Category.id_comp _)
    (by rw [Over.comp_left, ← h']; exact Category.id_comp _)
  rw [← MonObj.comp_mul, Over.comp_left] at key
  rw [← key]
  exact (Category.id_comp _).symm

theorem pull_one (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) : (1 : Over.mk t ⟶ A₁).left ≫ φ₁ = (1 : T' ⟶ A).left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨hPb, -⟩ := hP'
  have hw : ((1 : Over.mk t ⟶ A₁).left ≫ φ₁) ≫ A.hom = T'.hom := by
    rw [Category.assoc, hPb.w, ← Category.assoc, Over.w (1 : Over.mk t ⟶ A₁)]
    exact ht
  let c : T' ⟶ A := Over.homMk _ hw
  have hc := pull_mul hP T' t ht (g := 1) (g' := 1) (a := c) (a' := c) rfl rfl
  rw [_root_.mul_one] at hc
  have hcc : c * c = c := by
    apply Over.OverMorphism.ext
    exact hc.symm
  have h1 : c = 1 := mul_eq_left.mp hcc
  show c.left = _
  rw [h1]

theorem pull_inv (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) {g : Over.mk t ⟶ A₁} {a : T' ⟶ A}
    (h : g.left ≫ φ₁ = a.left) : (g⁻¹).left ≫ φ₁ = (a⁻¹).left := by
  have hP' := hP
  unfold IsGrpPullback at hP'
  obtain ⟨hPb, -⟩ := hP'
  have hw : ((g⁻¹).left ≫ φ₁) ≫ A.hom = T'.hom := by
    rw [Category.assoc, hPb.w, ← Category.assoc, Over.w (g⁻¹)]
    exact ht
  let c : T' ⟶ A := Over.homMk _ hw
  have hc := pull_mul hP T' t ht (g := g) (g' := g⁻¹) (a := a) (a' := c) h rfl
  rw [_root_.mul_inv_cancel, pull_one hP T' t ht] at hc
  have hac : a * c = 1 := by
    apply Over.OverMorphism.ext
    exact hc.symm
  have h1 : c = a⁻¹ := eq_inv_of_mul_eq_one_right hac
  show c.left = _
  rw [h1]

theorem pull_pow (hP : IsGrpPullback A₁ A x φ₁) (T' : Over S) (t : T'.left ⟶ T)
    (ht : t ≫ x = T'.hom) {g : Over.mk t ⟶ A₁} {a : T' ⟶ A}
    (h : g.left ≫ φ₁ = a.left) (n : ℕ) : (g ^ n).left ≫ φ₁ = (a ^ n).left := by
  induction n with
  | zero => simpa using pull_one hP T' t ht
  | succ n ih => rw [pow_succ, pow_succ]; exact pull_mul hP T' t ht ih h

end UpperTheory.SubRep
