import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

def TopExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ (Xo : ∀ l : Level H, Moduli D l) (n : ℕ), AuxiliaryInertOddPrime H n →
      ∃ J : ℕ, 1 ≤ J ∧ ∃ (T : Top Xo n (n ^ J)) (k : ℕ), Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2))

theorem TopExists.nonempty_top (h : TopExists) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D : Datum H) (hD : 1 ≤ D.p + D.q) (Xo : ∀ l : Level H, Moduli D l) (n : ℕ) (hn : AuxiliaryInertOddPrime H n) :
    ∃ J : ℕ, 1 ≤ J ∧ Nonempty (Top Xo n (n ^ J)) := by
  obtain ⟨J, hJ, T, -⟩ := h E H D hD Xo n hn
  exact ⟨J, hJ, ⟨T⟩⟩

namespace FullLevel

theorem natAbs_discr_dvd : (NumberField.discr HostModel.E21).natAbs ∣ 21 ^ Nat.totient 21 := by
  have h := IsCyclotomicExtension.Rat.natAbs_discr 21 HostModel.E21
  exact h ▸ Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (by norm_num))

theorem Prime_five : AuxiliaryInertOddPrime HostModel.host 5 := by
  refine ⟨by norm_num, by decide, ?_, fun h => ?_⟩
  · rw [HostModel.host_d]; decide
  · have h₁ : 5 ∣ 21 ^ Nat.totient 21 := (Int.natCast_dvd.1 h).trans natAbs_discr_dvd
    have h₂ := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h₁
    omega

theorem not_Prime : ¬ AuxiliaryInertOddPrime HostModel.host 7 ∧ ¬ AuxiliaryInertOddPrime HostModel.host 11 := by
  refine ⟨fun h => h.2.2.1 ?_, fun h => h.2.2.1 ?_⟩ <;> rw [HostModel.host_d] <;> decide

theorem hypotheses_inhabited (h : N1ab) :
    ∃ (H : Host HostModel.E21) (D : Datum H) (_ : ∀ l : Level H, Moduli D l), D.p = 1 ∧ D.q = 1 ∧ 1 ≤ D.p + D.q ∧
      AuxiliaryInertOddPrime H 5 ∧ ∀ J : ℕ, ∃ l : Level H, l.A = 5 ^ J :=
  ⟨HostModel.host, HostModel.hypDatum _, fun l => (h _ _ (HostModel.hypDatum _) l (by simp)).some, rfl, rfl, by simp,
    Prime_five, fun J => ⟨HostModel.level _ (5 ^ J) (by positivity), rfl⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end FullLevel

end GlobalTheory.Models

end
