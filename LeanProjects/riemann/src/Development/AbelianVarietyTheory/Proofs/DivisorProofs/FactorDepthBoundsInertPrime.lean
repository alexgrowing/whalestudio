import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentDetPowDependsOnPIKStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentLeDetDepthAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupRootsOfUnityTypedLieRanksStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ¬ (p : ℤ) ∣ discr E → InertInK H p → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → ∃ A B : ℝ, FacBetween Xo la f k A B ∧ B - A ≤ boundInert p Dw.q (rk f) k := by
  intro E _ _ _ H Dw l Xo c p _ la hdisc hinert f k hpsi
  letI := H.starRing
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.dividedPowerContent_detPow_depends_on_p_i_k p Fact.out (rk f) k
  have hFGT := GlobalTheory.T.formalGroup_rootsOfUnity_typed_lieRanks E H Dw l Xo c (fun _ => rfl) p hdisc
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hbd : boundInert p Dw.q (rk f) k =
      2 * ((rk f : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) + 2 * ((Dw.q : ℕ) : ℝ) * (k : ℝ) / ((p : ℝ) - 1) := rfl
  refine ⟨κ - boundInert p Dw.q (rk f) k, κ, fun T io e ho y => ⟨le_nuFac fun Ch X => ?_, fun _ => ?_⟩, by linarith⟩
  · obtain ⟨hfrob, htyp⟩ := hFGT T io X
    obtain ⟨h, hh, -, lab, hlab, d', G', ty, I, P, -, ⟨mu⟩, -, hcard, hfr⟩ := htyp y Ch f.1
    have hf0 : f.1 = lab 0 := hlab.1.symm
    obtain ⟨hsat, hsupp, hnu⟩ := hfr 0 f hf0
    have hiff := (hfrob (lab 0) (lab (0 + 1)) (hlab.2.1 0)).2 hinert
    have hnot : ¬ InPsi H (lab (0 + 1)) := fun h1 =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both H f.1 ⟨hpsi, by rw [hf0]; exact hiff.1 h1⟩
    have hc1 : (Finset.univ.filter fun a => ty a = (0 : ZMod h) + 1).card ≤ Dw.q := by
      have := hcard (0 + 1)
      rw [if_neg hnot, Fintype.card_subtype] at this
      exact this.le
    have hd2 := GlobalTheory.FGDepth.InertBound.content_le_detDepth_add X.C (vX_vp X) p Fact.out (vX_vp_p X) d' h hh ty G' mu
      0 Dw.q (rk f) k hc1 _ hsat hsupp
    rw [hκ X.C (vX_vp X) (vX_vp_p X), ← hbd] at hd2
    rw [hnu k, EReal.coe_sub]
    exact EReal.sub_le_of_le_add hd2
  · obtain ⟨Ch⟩ := hch T io y
    obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine (nuFac_le Ch X f k).trans ?_
    rw [← hκ X.C (vX_vp X) (vX_vp_p X)]
    exact h1.2.1

end GlobalTheory.RefSum
