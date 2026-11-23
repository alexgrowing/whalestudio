import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthEqZeroOfLtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_zero_boundAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  intro E _ _ _ H Dw l Xo c p _ la f k
  letI := H.starRing
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hB : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      0 ≤ nuFacC Ch X f k ∧ nuFacC Ch X f k ≤ ((boundAll p (rk f) k : ℝ) : EReal) ∧ (k < p → nuFacC Ch X f k = 0) := by
    intro T io y Ch X
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine ⟨h1.1, ?_, fun hk => GlobalTheory.T.formalGroupDeterminantPowDepth_eq_zero_of_lt_prime X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f) hk⟩
    have h2 := h1.2.2
    unfold boundAll
    exact h2
  have hmain : ∀ B : ℝ, (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p), nuFacC Ch X f k ≤ (B : EReal)) → FacBetween Xo la f k 0 B := by
    intro B hb T io e ho y
    refine ⟨?_, fun _ => ?_⟩
    · rw [EReal.coe_zero]
      exact le_nuFac fun Ch X => (hB T io y Ch X).1
    · obtain ⟨Ch⟩ := hch T io y
      obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
      exact (nuFac_le Ch X f k).trans (hb T io y Ch X)
  refine ⟨hmain _ fun T io y Ch X => (hB T io y Ch X).2.1, fun hk => hmain 0 fun T io y Ch X => ?_⟩
  rw [(hB T io y Ch X).2.2 hk, EReal.coe_zero]

end GlobalTheory.RefSum
