import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section

namespace GlobalTheory.Ex.Arch

theorem exists_pull_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f) :
    ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ φ = φ ≫ f.left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ G'}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let f' : G' ⟶ G' := Over.homMk (hg.1.lift (φ ≫ f.left) G'.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : f'.left ≫ φ = φ ≫ f.left := hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), pushPt hg.1.w (x ≫ f') = pushPt hg.1.w x ≫ f := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ G'), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  refine ⟨f', isMonHom_of_mul _ fun T x y => inj ?_, ha⟩
  rw [pa, pm, pm, pa, pa, MonObj.mul_comp]

theorem fibGrp : FibGrpSt := by
  intro R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨-, P', φ, w, u, hΛ, hg, -, hAH, -, -, hlift, hex, hfr⟩ := hF
  subst hΛ
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv hg (𝟙_ (Over (Sp ℂ))) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have hee : ∀ z, ex z = e (u.ex z) := fun z => Over.OverMorphism.ext ((hex z).trans (he _).symm)
  have hadd : ∀ z w, ex (z + w) = ex z * ex w := fun z w => by
    rw [hee, hee, hee, u.ex_add]
    exact map_mul e _ _
  have hker : ∀ z, ex z = 1 ↔ z ∈ u.Λ := fun z => by
    rw [hee, ← u.ker]
    exact e.map_eq_one_iff
  refine ⟨u.discrete, u.full, hAH.1, hAH.2.1, hAH.2.2.1, fun l m => FrameValue.chi_add P'.isLB hAH l m, hadd,
    fun y => ?_, hker, fun l z => ?_, fun f hf => ?_⟩
  · obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := u.ex_onto x
    exact ⟨z, (hee z).trans hx⟩
  · have hi := FrameValue.le_chartAt P'.isLB (u.ex z).left
    set i := FrameValue.chartAt P'.isLB (u.ex z).left
    have h₁ : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker _).2 l.2, _root_.mul_one]
    have h₂ : ex (z + l) = ex z := by rw [hee, hee, h₁]
    have a := hfr z i hi
    have b := hfr (z + l) i (by rw [h₁]; exact hi)
    rw [h₁, h₂] at b
    rw [a, b, hAH.2.2.2 l i z hi]
    simp only [hermForm]
    ring
  · obtain ⟨f', hf', hc⟩ := exists_pull_endo hg f hf
    obtain ⟨F, hF⟩ := hlift f' hf'
    have hF' : ∀ z, ex (F z) = ex z ≫ f := fun z => Over.OverMorphism.ext (by
      rw [Over.comp_left, hex, hex, hF, Over.comp_left, Category.assoc, hc, Category.assoc])
    refine ⟨F, hF', fun G hG => ?_⟩
    have hm : ∀ z, (G - F) z ∈ u.Λ := fun z => by
      rw [← hker]
      have h := hadd ((G - F) z) (F z)
      rw [LinearMap.sub_apply, sub_add_cancel, hG, hF'] at h
      exact mul_eq_right.1 h.symm
    haveI := u.discrete
    have hc : Continuous fun w => (⟨(G - F) w, hm w⟩ : u.Λ) :=
      (G - F).continuous_of_finiteDimensional.subtype_mk _
    refine sub_eq_zero.1 (LinearMap.ext fun z => ?_)
    have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
    simpa using congrArg Subtype.val this

end GlobalTheory.Ex.Arch

end
