import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QWeilZeroCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionStepLogCanonicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LcCutTwoClosedPointsOneCentreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem add_le_sum_Icc_of_lt (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) {n i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) {d : ℚ} (hd : d ≤ ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε)) :
    d + (h (i + 1) + ε) ≤ ∑ e ∈ Finset.Icc (i + 1) n, (h e + ε) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : i + 1 ≤ n), Finset.sum_cons]
  have : ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Ioc (i + 1) n, (h e + ε) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => by simp only [Finset.mem_Icc, Finset.mem_Ioc] at he ⊢; omega)
      fun e _ _ => (hpos e).le
  linarith

theorem sum_Icc_le_sum_Icc_one (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) (n j : ℕ) :
    ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    fun e _ _ => (hpos e).le

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem two_point_induction : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair →
    GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ)
    (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m →
    IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) →
    IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) →
    (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e →
      topologicalKrullDim (closure ({z} : Set X)) = e →
      2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X))
        fun _ : Fin e => N : ℤ)) → 0 < ε →
    ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧
      ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨
        (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim
  letI := algebraΓOfHom p
  intro Δ m G N ε h x₁ x₂ hΔ hklt hm hG hNa hc₁ hc₂ hne hh hint hε
  have hpos : ∀ e, 0 < h e + ε := fun e => add_pos (hh e) hε

  have hξ : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hdimξ : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [genericPoint_closure,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hdim]

  have hn : 1 ≤ n := by
    obtain ⟨e, -, he, he1⟩ := GlobalTheory.T.exists_topologicalKrullDim_closure_point_le X n (genericPoint X) hdim
    have hen : e = n := by
      rw [hdimξ] at he; exact_mod_cast he.symm
    subst hen
    by_cases h₁ : x₁ = genericPoint X
    · exact he1 x₂ (hξ x₂) fun h₂ => hne (h₁.trans h₂.symm)
    · exact he1 x₁ (hξ x₁) h₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have key : ∀ j, j ≤ k → ∀ (D : X → ℚ) (d : ℚ), 0 ≤ d →
      d ≤ ∑ e ∈ Finset.Icc (j + 1) (k + 1), (h e + ε) → QNum p N d D →
      ((LcCut p (k + 1) (Δ + D) x₁ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
        (LcCut p (k + 1) (Δ + D) x₂ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) →
      ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 (k + 1), (h e + ε) ∧ QNum p N d D ∧
        ((LcCut p (k + 1) (Δ + D) x₁ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
          (LcCut p (k + 1) (Δ + D) x₂ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjk D d hd0 hd hQ hcut
    have hd1 := hd.trans (sum_Icc_le_sum_Icc_one h ε hpos (k + 1) j)
    rcases hcut with ⟨hc, hnk⟩ | ⟨hc, hnk⟩
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₁ x₂ j hΔ hklt hm
          hG hNa hc₁ hc₂ hne hh hint hε hQ hd0 hc hnk with h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inl ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₂ x₁ j hΔ hklt hm
          hG hNa hc₂ hc₁ hne.symm hh (fun z e hz => hint z e hz.symm) hε hQ hd0 hc hnk with
        h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inr ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'.symm

  have hlc : ∀ x, LcAt p (k + 1) (Δ + 0) x := fun x => by rw [add_zero]; exact (hklt x).lcAt
  have hdimξ' : topologicalKrullDim (closure ({genericPoint X} : Set X)) = ((k + 1 : ℕ) : WithBot ℕ∞) :=
    hdimξ
  obtain ⟨D', d', hd'0, hd', hQ', hc'⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p (k + 1) hproj hdim Δ m G N 0
    0 (h (k + 1)) x₁ x₂ (genericPoint X) k hΔ hklt hm hG hNa (qNum_zero_zero X p hproj N) le_rfl
    hc₁ hc₂ (hlc x₁) (hlc x₂) (hξ x₁) (hξ x₂) (Or.inl rfl) hdimξ' (hh _)
    (hint (genericPoint X) (k + 1) (Or.inl (hξ x₁)) (by omega) hdimξ')
  refine key k le_rfl D' d' hd'0 ?_ hQ' hc'
  rw [Finset.Icc_self, Finset.sum_singleton]
  linarith [hε]

end GlobalTheory.PairStep
