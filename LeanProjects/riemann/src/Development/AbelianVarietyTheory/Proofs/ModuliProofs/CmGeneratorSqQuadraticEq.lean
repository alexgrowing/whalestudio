import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

namespace GlobalTheory.CMGeneratorSquareModuli

open NumberField

theorem cm_generator_sq_quadratic_eq {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ k : ℤ, H.w0 * H.w0 = H.w0 - (k : NumberField.RingOfIntegers E) := by
  have hm := H.d_mod
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (H.d : ℤ) + 1 = 4 * k := ⟨((H.d : ℤ) + 1) / 4, by omega⟩
  refine ⟨k, ?_⟩
  have hkc : (H.d : NumberField.RingOfIntegers E) + 1 = 4 * (k : NumberField.RingOfIntegers E) := by
    have := congrArg (fun z : ℤ => (z : NumberField.RingOfIntegers E)) hk
    push_cast at this
    exact this
  have h4 : (4 : NumberField.RingOfIntegers E) * (H.w0 * H.w0 - (H.w0 - (k : NumberField.RingOfIntegers E))) = 0 := by
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hkc
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · exact sub_eq_zero.mp h

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E},
    a ∈ Algebra.adjoin ℤ ({ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H} : Set (NumberField.RingOfIntegers E)) →
    ∃ u v : ℤ, a = (u : NumberField.RingOfIntegers E) + (v : NumberField.RingOfIntegers E) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  obtain ⟨k, hk⟩ := cm_generator_sq_quadratic_eq H
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    exact ⟨u1 + u2, v1 + v2, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u1, v1, rfl⟩ := hx
    obtain ⟨u2, v2, rfl⟩ := hy
    refine ⟨u1 * u2 - v1 * v2 * k, u1 * v2 + u2 * v1 + v1 * v2, ?_⟩
    push_cast
    linear_combination ((v1 : NumberField.RingOfIntegers E) * v2) * hk

end GlobalTheory.CMGeneratorSquareModuli
