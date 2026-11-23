import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.CompanionTheory.RgEisSign

variable {k : Type} [Field k] [NumberField k]

open scoped Classical in

def even_im_hermitian_sub (ω : HeckeCharacter k) (w : {w : InfinitePlace k // w.IsReal}) : ℕ :=
  if ω.realComponent w.2 (-1) = 1 then 0 else 1

theorem realComponent_coe (ω : HeckeCharacter k) (h : IsOfFinOrder ω)
    (w : {w : InfinitePlace k // w.IsReal}) (x : ℝˣ) :
    (ω.realComponent w.2 x : ℂ) = if 0 < (x : ℝ) then (1 : ℂ) else (-1) ^ even_im_hermitian_sub ω w := by
  split_ifs with hx
  · rw [ω.realComponent_eq_one_of_isOfFinOrder h w.2 hx]; simp
  · have hneg : (x : ℝ) < 0 := lt_of_le_of_ne (not_lt.1 hx) x.ne_zero
    have hpos : 0 < ((-x : ℝˣ) : ℝ) := by simpa using hneg
    have hx' : x = (-1) * (-x) := by simp
    have hc : ω.realComponent w.2 (-1) * ω.realComponent w.2 (-1) = 1 := by
      rw [← map_mul]; simp
    rw [hx', map_mul, ω.realComponent_eq_one_of_isOfFinOrder h w.2 hpos, mul_one]
    unfold even_im_hermitian_sub
    split_ifs with h1
    · rw [h1]; simp
    · have h2 : ((ω.realComponent w.2 (-1) : Circle) : ℂ) * ((ω.realComponent w.2 (-1) : Circle) : ℂ) = 1 := by
        rw [← Circle.coe_mul, hc]; simp
      rcases mul_self_eq_one_iff.1 h2 with h3 | h3
      · exact absurd (Circle.ext (by simpa using h3)) h1
      · simpa using h3

theorem real_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsReal}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) =
      if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℂ)
      else (-1) ^ even_im_hermitian_sub ω w := by
  have hs := realUnitsHom_surjective w.2 (infiniteComponent w.1 a)
  have hv : ((Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 : w.1.Completion →+* ℝ).toMonoidHom
      (infiniteComponent w.1 a) : ℝˣ) : ℝ) = (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w := rfl
  rw [← hs, ← hv]
  exact realComponent_coe ω h w _

theorem complex_factor (ω : HeckeCharacter k) (h : IsOfFinOrder ω) (a : (InfiniteAdeleRing k)ˣ)
    (w : {w : InfinitePlace k // w.IsComplex}) :
    (ω.infiniteComponent w.1 (infiniteComponent w.1 a) : ℂ) = 1 := by
  rw [← complexUnitsHom_surjective w.2 (infiniteComponent w.1 a)]
  have := ω.complexComponent_eq_one_of_isOfFinOrder h w.2
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 : w.1.Completion →+* ℂ).toMonoidHom
      (infiniteComponent w.1 a))
  exact congrArg (fun c : Circle => (c : ℂ)) this |>.trans (by simp)

theorem signChar : PositivityTheory.RgEis.TF.SignChar := by
  intro k _ _ ω h
  have hf : IsOfFinOrder ω :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, by rw [pow_two]; exact h⟩
  refine ⟨even_im_hermitian_sub ω, fun a => ?_⟩
  rw [HeckeCharacter.toIdele_ofInfinite]
  have h1 : ((∏ w, ω.infiniteComponent w (infiniteComponent w a) : Circle) : ℂ) =
      ∏ w, (ω.infiniteComponent w (infiniteComponent w a) : ℂ) :=
    map_prod Circle.coeHom (fun w => ω.infiniteComponent w (infiniteComponent w a)) Finset.univ
  rw [h1, InfinitePlace.prod_eq_prod_mul_prod, Finset.prod_eq_one (fun w _ => complex_factor ω hf a w),
    mul_one]
  exact Finset.prod_congr rfl fun w _ => real_factor ω hf a w

end GlobalTheory.CompanionTheory.RgEisSign
