import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AutomorphicArithmetic.CMTraceForms.Places
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtSmallOddInertPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmFieldStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem oscLe_eOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE vd S R hvd h2 h2S hdR hR p _
  have hram := GlobalTheory.T.depthOscillation_zero_above_and_degreeBound E H Dw l Xo c F k m M Mb Sm cx hS hE p
  have hMb : 0 ≤ Mb := hE.1
  have hp : p.Prime := Fact.out
  have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hF : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hFmMb : (0 : ℝ) ≤ F * m * Mb := by positivity
  unfold eOf
  split_ifs with h1 hS' h3 h4
  · exact hram.1 h1
  · exact GlobalTheory.T.depth_oscillation_le_at_two_cmField E H Dw l Xo c F k m M Mb Sm cx hS hE p (vd p) (hvd p) (h2 p hS')
  · exact hram.2
  all_goals
    have hpM : p ≤ M := Nat.le_of_not_lt h1
    have h2' : p ≠ 2 := fun h => hS' (h ▸ h2S)
    have hpd : ¬ (p : ℤ) ∣ discr E := hR p hp hS' h3
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := le_trans hp.one_lt.le hpM
      exact_mod_cast this
    have hlog : 0 ≤ Real.logb p M := Real.logb_nonneg (by exact_mod_cast hp.one_lt) hM1
    by_cases hsq : IsSquare (-(H.d : ZMod p))
    · have hd0 : (H.d : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdv
        have : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).1 hdv
        exact h3 (this ▸ hdR)
      have hs := GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd ⟨hd0, hsq⟩
      refine OscLe.mono Xo hs ?_
      first
      | (unfold eSmall
         have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         have hB : (0 : ℝ) ≤ F * (m + 1) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) := by positivity
         linarith)
      | (have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         linarith)
    · first
      | exact GlobalTheory.T.depthOscillation_le_at_small_odd_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd hsq (by exact_mod_cast hM1)
      | exact GlobalTheory.T.depthOscillation_large_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p hpd hsq (by omega)

end GlobalTheory.RefSum
