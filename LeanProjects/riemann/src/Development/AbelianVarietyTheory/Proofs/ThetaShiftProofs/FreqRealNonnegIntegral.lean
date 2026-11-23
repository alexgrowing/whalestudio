import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.FjFreq

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem exists_emb_of_freq (la : Wt X.Ψ r) (ν : X.Ψ → ℝ)
    (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) :
    ∃ ω : E, ∀ τ : X.Ψ, (ν τ : ℂ) = τ.1 ω := by
  refine X.exists_emb_eq (fun τ => (ν τ : ℂ)) fun γ => ?_
  have hN : ((X.m * X.chiOrd la : ℕ) : ℝ) ≠ 0 := by
    have := Nat.mul_pos X.m_pos (chiOrd_pos X la); positivity
  have hγ : IsIntegral ℤ (γ : E) := RingOfIntegers.isIntegral_coe γ
  have hcγ : IsIntegral ℤ (cc (γ : E)) := map_isIntegral_int (IsCMField.complexConj E) hγ
  have ha : cc ((γ : E) + cc (γ : E)) = (γ : E) + cc (γ : E) := by
    rw [cc_add', cc_cc', add_comm]
  obtain ⟨k, hk⟩ := hν _ ((mem_periods_iff X la _).2 ⟨_, ha, hγ.add hcγ, rfl⟩)
  refine ⟨(k : ℚ) / (4 * (X.m * X.chiOrd la : ℕ)), ?_⟩
  have h1 : ∑ τ, ν τ * per X la ((γ : E) + cc (γ : E)) τ =
      2 * ((X.m * X.chiOrd la : ℕ) : ℝ) * ∑ τ : X.Ψ, ν τ * (τ.1 (γ : E)).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [per, map_add, emb_cc', Complex.add_re, Complex.conj_re]
    ring
  rw [h1] at hk
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, ← hk]
  field_simp
  norm_num

theorem fj_transv (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {s : E} (hs : cc s = s) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hγm : (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0)) (hχ : X.χ la γ = 1) :
    X.fj la ξ ν P (X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) x) = X.fj la ξ ν P x := by
  have hact : ∀ y, lact γ y = X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) y := by
    intro y
    funext τ
    simp only [lact, Data.flow]
    rw [hγm, transvMat_map X ξ τ _ _ ?_]
    rw [map_mul, emb_kappa, ← emb_real hs]
    ring
  have key : ∀ t : X.Ψ → ℝ, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) x)) =
      P (X.flow ξ (fun τ => (t τ : ℂ)) x) := by
    intro t
    rw [flow_flow X hξ.2.1, add_comm, ← flow_flow X hξ.2.1, ← hact]
    exact (hP.2.2 γ hγ _ (flow_real_mem_dom X hξ.2.1 t x hx)).trans (by rw [hχ, one_mul]; rfl)
  unfold Data.fj
  simp only [key]

end GlobalTheory.FjFreq

namespace GlobalTheory.FjFreq

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

theorem freq_real_nonneg_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∃ ν₀ : E, cc ν₀ = ν₀ ∧ (∀ τ : X.Ψ, ν τ = (τ.1 ν₀).re) ∧ (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) ∧ ∀ s : E, cc s = s → (∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0) ∧ X.χ la γ = 1) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m := by
  intro E _ _ _ r X la P hP ξ hξ ν x hx hne
  have hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    by_contra h
    exact hne (by unfold Data.fj; rw [if_neg h])
  obtain ⟨ω, hω⟩ := exists_emb_of_freq X la ν hν
  have hre : ∀ τ : X.Ψ, ν τ = (τ.1 ω).re := fun τ => by rw [← hω, Complex.ofReal_re]
  obtain ⟨C, hC⟩ := hP.2
  have hnn := (moderateCoefficientPositivity_holds r X la P C 0 hP.1 (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  refine ⟨ω, ?_, hre, ?_, ?_⟩
  · obtain ⟨τ⟩ := X.nonempty_Psi
    apply τ.1.injective
    rw [emb_cc', ← hω, Complex.conj_ofReal]
  · intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact (hre ⟨σ, hσ⟩) ▸ hnn ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := (X.conj_mem_iff σ).2 hσ
      have h1 := hnn ⟨_, hc⟩
      rw [hre] at h1
      simpa [ComplexEmbedding.conjugate_coe_eq] using h1
  · rintro s hs ⟨γ, hγ, hγm, hχ⟩
    have h1 := X.fj_flow_real la ξ hξ ν P hP.1 hP.2 x hx (fun τ => (τ.1 s).re)
    rw [fj_transv X la P hP.1 hξ ν hx hs hγ hγm hχ] at h1
    have h2 : Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (((τ.1 s).re : ℝ) : ℂ)) = 1 :=
      mul_right_cancel₀ hne (by rw [one_mul]; exact h1.symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨n, ?_⟩
    have h3 : ((Algebra.trace ℚ E (ω * s) : ℚ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * (((τ.1 s).re : ℝ) : ℂ) := by
      rw [X.trace_eq_Psi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, ← hω, emb_real hs, Complex.ofReal_re, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h4 : ((Algebra.trace ℚ E (ω * s) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ hpi
      rw [h3, ← hn]
      ring
    exact_mod_cast h4

end GlobalTheory.FjFreq
