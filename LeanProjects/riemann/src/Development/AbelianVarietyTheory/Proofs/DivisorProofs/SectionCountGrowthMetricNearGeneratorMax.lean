import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountGrowthExponentialRadiiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFunctionFieldQuotientSubfieldEqDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundCountRankAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmpleStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem lc_exp_bounds : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ κ t : ℝ, 0 < κ → κ ≤ 1 → 0 < t → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, gdeg P.L D / D.factorial * t - ε ≤ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ∧ P.lc m 1 (Real.exp (t * m)) / (m : ℝ) ^ (D + 1) ≤ gdeg P.L D / D.factorial * (t - Real.log κ / e) + ε := by
  intro hA k _ X _ p D hp P hL e x hx κ t hκ hκ1 ht h1 h2 ε hε
  have hdeg := GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree hA k X p D hp P hL e x hx
  have hup := GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample k X p D hp P hL e x hx
  have hlo := GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample k X p D hp P hL e x hx
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hfin : ∀ (m : ℕ) (R : ℝ), 0 ≤ R → (P.Bl m 1 R).Finite := by
    intro m R hR
    obtain ⟨c, C, _, h⟩ := hup m 1
    have := ((h 0).2.2 R κ hR hκ h2).1
    simpa using this
  have key := GlobalTheory.T.count_growth_exponential_radii D e (Module.finrank (ratF x) X.functionField) (fun m R => (P.Bl m 1 R).ncard) κ t
    hx.pos hκ hκ1 ht
    (fun m R R' hR hRR' => Set.ncard_le_ncard
      (fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans hRR'⟩) (hfin m R' (hR.trans hRR')))
    (fun s _ => by
      obtain ⟨c, C, hC, h⟩ := hlo s 1
      obtain ⟨c', C', hC', h'⟩ := hup s 1
      refine ⟨c, c', C, C', hC, hC', fun q R hR => ⟨?_, ?_⟩⟩
      · have h3 := (h q).2 R hR h1
        have hf := hfin (e * (q + c) + s) (C * (q + D).choose D * R) (by positivity)
        have e1 : ((e * (q + c) + s : ℕ) : ℤ) = e * (q + c : ℕ) + s := by push_cast; ring
        rw [← e1, ← hf.cast_ncard_eq] at h3
        exact_mod_cast h3
      · have h3 := ((h' q).2.2 R κ hR hκ h2).2
        have e1 : ((e * q + s : ℕ) : ℤ) = e * q + s := by push_cast; ring
        rw [← e1] at h3
        exact h3) ε hε
  have e2 : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) =
      gdeg P.L D / D.factorial := by
    rw [hdeg, mul_div_mul_left _ _ (pow_pos he D).ne']
  rw [e2] at key
  exact key

end GlobalTheory.HSAmp
