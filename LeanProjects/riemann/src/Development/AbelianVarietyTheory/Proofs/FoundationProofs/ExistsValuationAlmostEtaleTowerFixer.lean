import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityOfNormalFiniteIndexSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedFieldCyclotomicTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegralStatement

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.ValuationAlmostSeparation

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem orbit_finite (h : IsClo p Ω) (H : Subgroup (Gal p Ω)) (s : Ω) :
    (MulAction.orbit H s).Finite := by
  classical
  obtain ⟨P, hP0, hPs⟩ := (h.alg.isAlgebraic s)
  have hQ : P.map (algebraMap (O0 p) Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff h.inj).2 hP0
  refine (P.map (algebraMap (O0 p) Ω)).roots.toFinset.finite_toSet.subset ?_
  rintro _ ⟨g, rfl⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hQ, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  show Polynomial.aeval ((g : Gal p Ω) s) P = 0
  rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  simp [hPs]

theorem fix_top (H : Subgroup (Gal p Ω)) :
    Fix Ω (⊤ : Subgroup H) = Fix Ω H := by
  ext x
  constructor
  · intro hx g
    exact hx ⟨g, Subgroup.mem_top g⟩
  · intro hx g
    exact hx g.1

end GlobalTheory.ValuationAlmostSeparation

open GlobalTheory.ValuationAlmostSeparation

theorem GlobalTheory.ValuationAlmostSeparation.exists_valuation_almostSep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω), ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 ∧ ∀ S : Finset Ω, ∃ U : Subgroup ↥(⨅ n, Gn T n), U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix Ω U) ∧ AlmostSep v U := by
  intro p _ Ω _ _ hp2 hclo T
  obtain ⟨v, hint, hinv, hp0, hp1⟩ := GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral p Ω hclo
  refine ⟨v, hint, hinv, hp0, hp1, fun S => ?_⟩
  obtain ⟨U, hUn, hUf, hUS, hUsep⟩ := GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits Ω (↥(⨅ n, Gn T n)) S
    (fun s _ => orbit_finite hclo _ s)
  refine ⟨U, hUn, hUf, hUS, ?_⟩
  have hR := GlobalTheory.T.approxPthRoot_fixedField_cyclotomic_tower p Ω hp2 hclo T v hint hp0 hp1
  refine GlobalTheory.T.almostPurity_of_normal_finiteIndex_subgroup Ω v p (Fact.out) hp0 hp1 (↥(⨅ n, Gn T n)) (fun g x => hinv g.1 x)
    (T.ζ 1) (by simpa using T.prim 1) ?_ (by rw [fix_top]; exact hR) U hUn hUf hUsep
  intro g
  have hg : (g : Gal p Ω) ∈ Gn T 1 := (iInf_le (fun n => Gn T n) 1) g.2
  exact hg.1
