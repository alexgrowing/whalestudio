import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceExponentPrimeBound
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_exponent_prime_bound : Hypotheses2 → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → FlatExists Y.U (xiR D) → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtOf (T.Q.Dw j) u 0) q ≤ refExp_vp Y.U cst (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m) q + (((if q ∈ badPrimes T.Q.H Y.d.l₂ then (m * (D.R.f * D.R.r) * (different_vp D.host.E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  first | exact @GlobalTheory.RefSum.WFree.refExp_vp_le_shift | exact GlobalTheory.RefSum.WFree.refExp_vp_le_shift | (intros; apply GlobalTheory.RefSum.WFree.refExp_vp_le_shift <;> assumption)
