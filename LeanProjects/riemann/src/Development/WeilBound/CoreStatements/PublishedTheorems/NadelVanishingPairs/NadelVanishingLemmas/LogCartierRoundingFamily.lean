import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedgeStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMemStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ChartFormsDifferentialClosed
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EulerContractionChartForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTopStatement

set_option autoImplicit false

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem logCartier_rounding_family : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)
    (x : Fin n → Kˣ) (J : Finset (Fin n)) (γ : abelian₂ K →+* abelian₂ K) (Y : Type) [Nonempty Y] (A : Y → Subring K)
    (t : Y → Kˣ) (r : Y → Fin n → ℕ), (∀ y, AlgChart (A y) x) → (∀ y j, r y j < p) → IsCartierMap p x γ →
    ∀ (a : ℕ) (η : abelian₂ K), (∀ y, η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) a) →
    extD K η = 0 → ∃ ζ ξ : abelian₂ K, (∀ y, ζ ∈ chartForms (A y) x J (t y) a) ∧
      (∀ y q, q + 1 = a → ξ ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (a = 0 → ξ = 0) ∧ η = γ ζ + extD K ξ := by
  intro K _ p _ _ n x J γ Y _ A t r hA hr hγ a η hη hd
  obtain ⟨y0⟩ := ‹Nonempty Y›
  have hc : IsCoord x := (hA y0).coord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h, Q, π, hhom, hQw, hπ, -, -, hstab⟩ := GlobalTheory.T.cartier_projection_properties K p n x hc
  have hT : ∀ y, (∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) (q + 1),
        h η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) 0, h η = 0) ∧
      ∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q,
        Q η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q := by
    intro y
    exact hstab (fun q => chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q)
      (GlobalTheory.T.chart_forms_differential_closed K p (A y) n x J (t y) (r y) (hA y))
      (fun i θ hθ => GlobalTheory.T.euler_contraction_chart_forms K (A y) n x J _ i θ (hA y).mem hθ)
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hc
  obtain ⟨c, hcη⟩ : ∃ c : Finset (Fin n) → K, ∑ I, c I • logWedge x I = η :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (hsp ▸ Submodule.mem_top)
  choose g hg using fun I => hπ (c I)
  have hQη : Q η = ∑ I, g I ^ p • logWedge x I := by
    rw [← hcη, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQw, hg]
  refine ⟨∑ I, g I • logWedge x I, h η, ?_, ?_, ?_, ?_⟩
  · intro y
    have hm := (hT y).2.2 a η (hη y)
    rw [GlobalTheory.T.mem_chart_forms_iff] at hm
    obtain ⟨c', hc'0, hc'A, hc'eq⟩ := hm
    have heq : ∀ I, c' I = g I ^ p := by
      have h0 : ∑ I, (c' I - g I ^ p) • logWedge x I = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hc'eq, ← hQη, sub_self]
      intro I
      exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 I)
    rw [GlobalTheory.T.mem_chart_forms_iff]
    refine ⟨g, ?_, ?_, rfl⟩
    · intro I hI
      have h1 := hc'0 I hI
      rw [heq] at h1
      exact (pow_eq_zero_iff hp.ne').mp h1
    · intro I
      have h1 := hc'A I
      rw [heq] at h1
      exact GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem K p (A y) n x I J (t y) (r y) (g I) hp (hA y) (hr y) h1
  · intro y q hq
    subst hq
    exact (hT y).1 q η (hη y)
  · intro ha
    subst ha
    exact (hT y0).2.1 η (hη y0)
  · rw [map_sum]
    simp_rw [GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ]
    rw [← hQη]
    have h2 := hhom η
    rw [hd, map_zero, add_zero] at h2
    exact sub_eq_iff_eq_add'.mp h2

end GlobalTheory
