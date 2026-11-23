import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  intro X _ _ _ p n _ _ Γ B a b x hB hab
  obtain ⟨m', f, hm', hf, hBf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p B hB x
  have key : ∀ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), 0 < m →
      IsLogEqn p (Γ + b • B) η x m g →
      ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + a • B) η x m'' g'' ∧
        ∀ E : DivOver p, E.Through x → discrep E η m g ≤ discrep E η m'' g'' := by
    intro η m g hm hlog
    obtain ⟨m'', g'', hm'', hlog'', hd⟩ :=
      GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Γ + b • B) B η x m m' g f (a - b) hm hm' hlog hBf
    have e : Γ + b • B + (a - b) • B = Γ + a • B := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at hlog''
    refine ⟨m'', g'', hm'', hlog'', fun E hE => ?_⟩
    have h0 : (0 : ℚ) ≤ E.ord f := by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)
    have h1 : (0 : ℚ) ≤ (E.ord f : ℚ) / m' := div_nonneg h0 (Nat.cast_nonneg _)
    rw [hd E]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) h1]
  refine ⟨fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_, fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => lt_of_lt_of_le (hk E hE) (hle E hE)⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => le_trans (hk E hE) (hle E hE)⟩
