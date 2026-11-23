import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

theorem Wit.fac_alg : Wit.fac.Alg := by
  have hf : Wit.fac.f = 1 := rfl
  have hs : Star.star Wit.fac.e = Wit.fac.e := rfl
  have hi := Wit.fac.idem
  refine ⟨⟨1, one_pos, ?_⟩, ?_, 1, ?_⟩
  · rw [hf, mul_one, one_smul]
  · rw [hf, star_one]
  · rw [hf, hs, mul_one, one_mul, hi]

end GlobalTheory.Mum
