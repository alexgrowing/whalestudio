import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTopologicalKrullDimDiffOpenLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.GenCut

theorem isEmpty_of_topologicalKrullDim_lt_zero (T : Type) [TopologicalSpace T]
    (h : topologicalKrullDim T < ((0 : ℕ) : WithBot ℕ∞)) : IsEmpty T := by
  by_contra hT
  rw [not_isEmpty_iff] at hT
  obtain ⟨x⟩ := hT
  haveI : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim T := Order.krullDim_nonneg
  exact absurd h (not_lt.mpr (by simpa using h0))

theorem exists_sections_cover_closed (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X) (hL : L.IsLB)
    (n : ℕ) (u : Fin n → L.Sec) (hu : ⨆ i, nonzeroLocus (u i) = ⊤) (e : ℕ) :
    ∀ Z : Set X, IsClosed Z → topologicalKrullDim Z < (e : ℕ) →
      ∃ s : Fin e → L.Sec, ∀ x ∈ Z, ∃ i, x ∈ nonzeroLocus (s i) := by
  induction e with
  | zero =>
    intro Z _ h
    have := isEmpty_of_topologicalKrullDim_lt_zero Z h
    exact ⟨Fin.elim0, fun x hx => (this.false ⟨x, hx⟩).elim⟩
  | succ e ih =>
    intro Z hZ h
    obtain ⟨S, hS, hdim⟩ := GlobalTheory.T.exists_finite_topologicalKrullDim_diff_open_lt X Z hZ
    obtain ⟨t, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_finite_of_generated' k X p L hL n u hu S hS
    have hU : IsOpen ((nonzeroLocus t : X.Opens) : Set X) := (nonzeroLocus t).isOpen
    obtain ⟨s, hs⟩ := ih (Z \ ((nonzeroLocus t : X.Opens) : Set X)) (hZ.sdiff hU)
      (hdim _ hU (fun x hx => ht x hx) e h)
    refine ⟨Fin.cons t s, fun x hx => ?_⟩
    by_cases hxt : x ∈ nonzeroLocus t
    · exact ⟨0, by simpa using hxt⟩
    · obtain ⟨i, hi⟩ := hs x ⟨hx, hxt⟩
      exact ⟨i.succ, by simpa using hi⟩

theorem exists_generating_sections_of_dim_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ d : ℕ, topologicalKrullDim X ≤ d → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ s : Fin (d + 1) → L.Sec, ⨆ i, nonzeroLocus (s i) = ⊤ := by
  intro k _ _ X _ p L hL d hd n u hu
  have h1 : topologicalKrullDim (Set.univ : Set X) ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le X _
  have h2 : ((d : ℕ) : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self d
  obtain ⟨s, hs⟩ := exists_sections_cover_closed k X p L hL n u hu (d + 1) Set.univ isClosed_univ
    (lt_of_le_of_lt (h1.trans hd) h2)
  refine ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := hs x (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end GlobalTheory.GenCut
