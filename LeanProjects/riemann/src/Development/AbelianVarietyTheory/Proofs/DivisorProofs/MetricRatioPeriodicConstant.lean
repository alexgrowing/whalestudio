import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFundamentalDomainCovers
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TateUniq

theorem metric_eq_of_doubling : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (m h : Pt E g → ℝ) (φ : Pt E g → ℂ), (∀ P ∈ cov B g, 0 < m P) → (∀ P ∈ cov B g, 0 < h P) → (∀ l ∈ stdLat g, ∀ P ∈ cov B g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l P) * ‖j l P‖ ^ 2 = m P) → (∀ l ∈ stdLat g, ∀ P ∈ cov B g, h (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.transl τ l P) * ‖j l P‖ ^ 2 = h P) → (∀ b ∈ B, Continuous fun z => m (b, z)) → (∀ b ∈ B, Continuous fun z => h (b, z)) → (∀ P ∈ cov B g, m (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 P) = m P ^ 4 * ‖φ P‖ ^ 2) → (∀ P ∈ cov B g, h (GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.mulN 2 P) = h P ^ 4 * ‖φ P‖ ^ 2) → Set.EqOn m h (cov B g) := by
  intro g E _ _ B τ hτ j m k φ hm hk hmt hkt hmc hkc hm2 hk2
  set d : Pt E g → ℝ := fun P => Real.log (m P) - Real.log (k P) with hd
  have hmem : ∀ b ∈ B, ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov B g :=
    fun b hb _ => ⟨hb, Set.mem_univ _⟩

  have hper : ∀ b ∈ B, ∀ l ∈ stdLat g, ∀ z, d (b, z + per (τ b) l) = d (b, z) := by
    intro b hb l hl z
    have h1 := hmt l hl (b, z) (hmem b hb z)
    have h2 := hkt l hl (b, z) (hmem b hb z)
    simp only [transl] at h1 h2
    have hm' : 0 < m (b, z + per (τ b) l) := hm _ (hmem b hb _)
    have hk' : 0 < k (b, z + per (τ b) l) := hk _ (hmem b hb _)
    have hjp : 0 < ‖j l (b, z)‖ ^ 2 := by
      rcases (sq_nonneg ‖j l (b, z)‖).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, mul_zero] at h1
        exact absurd h1.symm (hm _ (hmem b hb z)).ne'
    simp only [hd]
    rw [← h1, ← h2, Real.log_mul hm'.ne' hjp.ne', Real.log_mul hk'.ne' hjp.ne']
    ring

  have hdbl : ∀ b ∈ B, ∀ z, d (b, (2 : ℤ) • z) = 4 * d (b, z) := by
    intro b hb z
    have hP := hmem b hb z
    have h1 := hm2 _ hP
    have h2 := hk2 _ hP
    simp only [mulN] at h1 h2
    have hm' := hm _ (hmem b hb ((2 : ℤ) • z))
    have hφ : 0 < ‖φ (b, z)‖ ^ 2 := by
      rcases (sq_nonneg ‖φ (b, z)‖).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, mul_zero] at h1
        exact absurd h1 hm'.ne'
    simp only [hd]
    rw [h1, h2, Real.log_mul (pow_pos (hm _ hP) 4).ne' hφ.ne',
      Real.log_mul (pow_pos (hk _ hP) 4).ne' hφ.ne']
    simp only [Real.log_pow]
    push_cast
    ring
  have hiter : ∀ b ∈ B, ∀ z, ∀ n : ℕ, d (b, ((2 : ℤ) ^ n) • z) = 4 ^ n * d (b, z) := by
    intro b hb z n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, hdbl b hb, ih, pow_succ']
      ring

  have hbd : ∀ b ∈ B, ∃ C : ℝ, ∀ z, |d (b, z)| ≤ C := by
    intro b hb
    have hdet : ((τ b).map Complex.im).det ≠ 0 := (hτ.2.2 b hb).2.det_pos.ne'
    have hcz : Continuous fun z => d (b, z) := by
      simp only [hd]
      exact ((hmc b hb).log fun z => (hm _ (hmem b hb z)).ne').sub
        ((hkc b hb).log fun z => (hk _ (hmem b hb z)).ne')
    have hcp : Continuous (per (τ b)) := by
      unfold per
      refine Continuous.add ?_ ?_
      · exact Continuous.matrix_vecMul (by fun_prop) continuous_const
      · fun_prop
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fl g)) (b := 1)).exists_bound_of_continuousOn
      (hcz.comp hcp).continuousOn
    refine ⟨C, fun z => ?_⟩
    obtain ⟨x, hx, l, hl, rfl⟩ := GlobalTheory.FundDom.fund_dom (τ b) hdet z
    rw [hper b hb l hl]
    simpa [Real.norm_eq_abs] using hC x hx

  intro P hP
  obtain ⟨b, z⟩ := P
  have hb : b ∈ B := hP.1
  obtain ⟨C, hC⟩ := hbd b hb
  have h0 : d (b, z) = 0 := by
    by_contra hne
    have hpos : 0 < |d (b, z)| := abs_pos.2 hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / |d (b, z)|) (by norm_num : (1 : ℝ) < 4)
    have h1 := hC ((2 : ℤ) ^ n • z)
    rw [hiter b hb z n, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n)] at h1
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hmP := hm _ hP
  have hkP := hk _ hP
  exact Real.log_injOn_pos (Set.mem_Ioi.2 hmP) (Set.mem_Ioi.2 hkP) (by simp only [hd] at h0; linarith)

end GlobalTheory.TateUniq
