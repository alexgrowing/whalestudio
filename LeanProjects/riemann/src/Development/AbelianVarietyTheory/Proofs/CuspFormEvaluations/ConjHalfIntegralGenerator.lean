import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds

namespace GlobalTheory.CMConjugationOfSquareRoot

open NumberField Complex
open scoped ComplexConjugate

theorem conj_eq_neg_of_sq_eq_neg {z : ℂ} {d : ℝ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    conj z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h0 | h0
    · exact h0
    · rw [h0] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hre0]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem complexConj_rt (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E ((H.rt : 𝓞 E) : E) = -((H.rt : 𝓞 E) : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq_eq_neg (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
  simpa using h

theorem conj_halfIntegralGenerator (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc ((H.w0 : 𝓞 E) : E) = (1 : E) - ((H.w0 : 𝓞 E) : E) := by
  have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.two_weight_eq_one_add_root
    push_cast at this
    exact this
  have h3 : (2 : E) * IsCMField.complexConj E (H.w0 : E) = 1 - (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add, map_one, complexConj_rt] at this
    have h22 : IsCMField.complexConj E (2 : E) = 2 := map_ofNat _ 2
    rw [h22] at this
    rw [this]; ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.cc
  apply mul_left_cancel₀ (two_ne_zero : (2 : E) ≠ 0)
  rw [h3, mul_sub, h2]; ring

theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ReciprocityTheory.ChartRestriction.G.FD.cc (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) = (1 : E) - (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H) : E) := fun H => conj_halfIntegralGenerator H

end GlobalTheory.CMConjugationOfSquareRoot
