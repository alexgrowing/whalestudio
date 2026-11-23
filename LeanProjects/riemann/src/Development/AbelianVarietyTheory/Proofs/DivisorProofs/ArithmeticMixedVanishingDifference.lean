import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtAdelicRootSymbolsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtAdelicRootSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtWholeSymbolReindexedStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag

namespace GlobalTheory.HTWholeVert

theorem arMix_comp (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB) (D : D7) (O : Setup D)
    (hO : O.Core) (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (p : ℕ) (hp : p.Prime) (y : Rt D.what₂.Tau O.N)
    (g : MvPolynomial (Vm D.what₂.Tau O.N) ℝ) :
    (arIn O.s O.Φ O.met.hm).arMix Sx R p (X (Sum.inr (true, 2)) * ((X (Sum.inl (false, y)) - X (Sum.inl (true, y))) * g)) = 0 := by
  rw [ArIn.arMix, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  obtain ⟨e, hF⟩ := GlobalTheory.T.flag_at_whole_symbol_reindexed h2 hH hRA hSW D O hO Sx R hR p hp c
  have hS : ∀ i, ∀ a ∈ ((arIn O.s O.Φ O.met.hm).whole (Function.update (ArIn.ind Sx) p true) R (e i) c :
      Sym D.host.E →₀ ℤ).support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R := by
    intro i a ha
    have key : a.1 = Function.update (ArIn.ind Sx) p true ∧ a.2.1 = some R := by
      change a ∈ (wholeSym (E := D.host.E) (Function.update (ArIn.ind Sx) p true) (some R) (e i)).support at ha
      generalize e i = l at ha
      cases l with
      | inl k =>
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
        exact ⟨rfl, rfl⟩
      | inr k =>
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
        exact ⟨rfl, rfl⟩
    rw [key.1]
    refine ⟨(Sx.finite_toSet.insert p).subset fun q hq => ?_, key.2⟩
    by_cases h : q = p
    · exact Or.inl h
    · right
      simpa [Function.update_of_ne h, ArIn.ind] using hq
  have h := GlobalTheory.T.flag_at_adelic_root_symbols h2 hH hRA hSW D O hO Sx R hR p hp c _ (fun i => (arIn O.s O.Φ O.met.hm).whole
    (Function.update (ArIn.ind Sx) p true) R (e i) c) hS hF 2 (by norm_num) y
    ((arIn O.s O.Φ O.met.hm).mixEv Sx R p c g) (GlobalTheory.PowerSumVert.mixEv_vars O.s O.Φ O.met.hm Sx R p c g)
  rw [Equiv.sum_comp e (fun l => X ((arIn O.s O.Φ O.met.hm).whole (Function.update (ArIn.ind Sx) p true) R l c) ^ 2)] at h
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_sub]
  simp only [ArIn.mixEv, aeval_X]
  rw [mul_assoc, MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_eq_zero]
  exact Or.inr h

theorem htWhole_mul_vert : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → ∀ (y : Rt D.what₂.Tau O.Y.N) (g : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℝ), O.Y.arMix Sx R p (X (Sum.inr (true, 2)) * ((X (Sum.inl (false, y)) - X (Sum.inl (true, y))) * g)) = 0 :=
  fun h2 hH hRA hSW D O hO Sx R hR p hp y g => arMix_comp h2 hH hRA hSW D O hO Sx R hR p hp y g

end GlobalTheory.HTWholeVert
