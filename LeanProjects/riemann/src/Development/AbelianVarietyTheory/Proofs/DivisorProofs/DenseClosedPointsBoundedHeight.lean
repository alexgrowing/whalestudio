import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsBoundClosePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensePointsRegularBoundedValuesStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

namespace GlobalTheory.CovHt

theorem denseBoundedHtAb : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp,
    ∃ S : Set (O.var c).X, (∀ b ∈ S, IsClosed ({b} : Set (O.var c).X)) ∧ Dense S ∧
      ∃ C : ℝ, ∀ b ∈ S, (O.met.ab c).ht b ≤ C := by
  intro _ _ D O hO c
  have hamp := hO.ample_ab c
  obtain ⟨x, P, h⟩ := hO
  have e := h.ab_eq
  have hmod : ∃ (M : Model (O.var c)) (L : GlobalTheory.HermLB M.p) (q : ℕ+), (O.met.ab c).Induced M L q 0 := by
    obtain ⟨M, L, q, hi, -⟩ := P.ab_model c
    exact ⟨M, L, q, e ▸ hi⟩
  have hsm : ∀ σ, (cxSt D.what₂.LL).mSmooth (O.var c) σ (O.met.ab c).D ((O.met.ab c).m σ) := by
    rw [e]; exact P.ab_smooth c
  obtain ⟨N, f, hU, hK⟩ := GlobalTheory.T.regular_functions_bound_close_points _ _ _ (O.met.ab c) hamp hmod hsm
  obtain ⟨S, hcl, hd, hreg, a, b, hb, hloc⟩ := GlobalTheory.T.dense_points_regular_bounded_values _ (O.var c) N f hU
  obtain ⟨K, hK'⟩ := hK a b hb
  exact ⟨S, hcl, hd, K, fun y hy => hK' y (hcl y hy) (hreg y hy) (hloc y hy).1 (hloc y hy).2⟩

end GlobalTheory.CovHt
