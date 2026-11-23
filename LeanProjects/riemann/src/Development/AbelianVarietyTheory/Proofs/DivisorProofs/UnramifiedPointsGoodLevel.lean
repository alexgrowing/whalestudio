import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOneStatement
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.UnramCM

theorem unramPts_of_cm : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) := by
  intro hP E _ _ _ H Dw l Xo c hpq hcase hg
  refine UnramPts.of_index_one fun Z w hw => ?_
  have hch : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal := by
    haveI := w.isMaximal
    haveI : Finite (𝓞 c.F ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    letI := Ideal.Quotient.field w.asIdeal
    refine ⟨ringChar (𝓞 c.F ⧸ w.asIdeal), CharP.char_is_prime (𝓞 c.F ⧸ w.asIdeal) _, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  obtain ⟨q, hq, hqw⟩ := hch
  have hqB : q ∉ badPrimes H l := fun h => hw q h hqw
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have h3 : 3 ≤ l.M' := le_trans l.three_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.dvd_lcm_left _ _))
  have hqd : ¬ q ∣ 2 * l.M' * H.d := fun h => hqB <| by
    have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) hD) hM
    rw [badPrimes, Nat.mem_primeFactors_of_ne_zero hne]
    refine ⟨hq, ?_⟩
    have : 2 * l.M' * H.d ∣ 2 * H.d * (discr E).natAbs * l.M' :=
      ⟨(discr E).natAbs, by ring⟩
    exact h.trans this
  obtain ⟨F', _, hdisc, hcurve⟩ := GlobalTheory.T.exists_field_unramified_curve hP E H l.M' q h3 hq hqd
  let K : IntermediateField ℚ ℂ := c.F ⊔ F'
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  have hle : c.F ≤ K := le_sup_left
  have hK : GlobalTheory.CompRat.CurveOver H K l.M' := fun τ hτ =>
    hcurve τ fun x hx => hτ x (le_sup_right (a := c.F) hx)
  obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.T.compositum_intermediateField_exists_place_valuation_eq c.F F' K hle rfl q hq hdisc w hqw
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field E H Dw l Xo c hpq hcase K hle hK Z
  exact GlobalTheory.T.exists_integralFramedPoint_completion_index_one E H Dw l Xo c hpq hg Z K y hy w 𝔭 h𝔭

end GlobalTheory.UnramCM
