import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_lcAt_add_of_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  intro X _ _ _ p n hp hn Γ A z x hN hA hoff hzx hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hlcz := ((GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Γ + A) x z hzx).2 hlc)
  obtain ⟨E, η, m, g, hη, hm, hlog, hC, hd⟩ := hN
  obtain ⟨m₀, D₀, hm₀, hEff, rfl⟩ := hA
  obtain ⟨m', f, hm', hreg, heq⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p (qWeil D₀ m₀) ⟨m₀, D₀, hm₀, hEff, rfl⟩ z
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ :=
    GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Γ (qWeil D₀ m₀) η z m m' g f 1 hm hm' hlog heq
  rw [one_smul] at hlog''
  have h1 := ((GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Γ + qWeil D₀ m₀) η z m'' g'' hη hm'' hlog'').1 hlcz) E hC.1
  rw [hdisc E, one_mul] at h1
  have hf0 : 0 ≤ E.ord f := (E.ord_nonneg_iff f).2 (hC.1 _ hreg)
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have hfle : (E.ord f : ℚ) / m' ≤ 0 := by linarith
  have hfle' : (E.ord f : ℚ) ≤ 0 := by
    rwa [div_le_iff₀ hm'q, zero_mul] at hfle
  have hord : E.ord f = 0 := by
    have : E.ord f ≤ 0 := by exact_mod_cast hfle'
    omega
  have hreg' := hC.2 f hreg hord
  apply hoff
  intro w hw
  by_cases hc : Order.coheight w = 1
  · obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
    rw [heq w hw F hF]
    have a : 0 ≤ F.ord f :=
      (F.ord_nonneg_iff f).2 ((hF _).2 (regAt_of_specializes hw hreg))
    have b : 0 ≤ F.ord f⁻¹ :=
      (F.ord_nonneg_iff _).2 ((hF _).2 (regAt_of_specializes hw hreg'))
    rw [F.ord_inv] at b
    have : F.ord f = 0 := by omega
    simp [this]
  · have : D₀.mult w = 0 := by
      by_contra h
      exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    simp [qWeil, this]

end GlobalTheory.PairStep
