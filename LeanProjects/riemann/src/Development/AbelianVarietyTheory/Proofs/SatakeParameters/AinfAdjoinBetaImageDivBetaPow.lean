import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat.BetaDiv

variable {l : ℕ} [Fact l.Prime]

theorem Sa_decomp (ϖ : Per.Fl l) (x : Per.AinfP l) (hx : x ∈ Sa ϖ) :
    ∃ a : Per.Ainf l, ∃ y ∈ Sa ϖ, x = algebraMap (Per.Ainf l) (Per.AinfP l) a + beta ϖ * y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, one_mem _, by rw [hx, map_zero, zero_add, mul_one]⟩
  | algebraMap r => exact ⟨r, 0, zero_mem _, by rw [mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    exact ⟨a + b, u + v, add_mem hu hv, by rw [map_add]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, v, hv, rfl⟩ := hy
    have hb : beta ϖ ∈ Sa ϖ := Algebra.subset_adjoin (Set.mem_singleton _)
    refine ⟨a * b, algebraMap (Per.Ainf l) (Per.AinfP l) a * v + u * algebraMap (Per.Ainf l) (Per.AinfP l) b
      + beta ϖ * u * v, ?_, by rw [map_mul]; ring⟩
    exact add_mem (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hv)
      (mul_mem hu (Subalgebra.algebraMap_mem _ _))) (mul_mem (mul_mem hb hu) hv)

theorem Sa_cancel_beta (ϖ : Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (c : Per.AinfP l) (hc : beta ϖ * c ∈ Sa ϖ) : c ∈ Sa ϖ := by
  obtain ⟨i1, i2, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  obtain ⟨hsurj, hker, hA, -, hdom, hinj, -⟩ := thetaP_facts l
  obtain ⟨hK1, hK2, -⟩ := hK ϖ hϖ
  obtain ⟨a, y, hy, hxy⟩ := Sa_decomp ϖ _ hc

  have ha : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    rw [hk, Ideal.mem_span_singleton']
    exact ⟨c - y, by linear_combination hxy⟩
  have hθ : Per.θ l a = 0 := by
    rw [← hker, RingHom.mem_ker, hA] at ha
    exact Subtype.ext (by simpa using ha)
  have hmem : a ∈ RingHom.ker (Per.θ l) := hθ
  have hK1' : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hK1
  rw [hK1', Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem

  have hne : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ≠ 0 := nonZeroDivisors.ne_zero hK2
  have hβ : beta ϖ ≠ 0 := by
    intro h0
    apply hne
    apply hinj
    have := l_mul_beta ϖ
    rw [h0, mul_zero] at this
    rw [map_sub, map_natCast, map_zero]
    linear_combination this
  have hlb := l_mul_beta ϖ
  have e : beta ϖ * c = beta ϖ * (y - ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) d) := by
    rw [hxy, ← hd, map_mul, map_sub, map_natCast]
    linear_combination (algebraMap (Per.Ainf l) (Per.AinfP l) d) * hlb
  rw [mul_left_cancel₀ hβ e]
  exact sub_mem hy (mul_mem (natCast_mem _ _) (Subalgebra.algebraMap_mem _ _))

theorem Sa_cancel_beta_pow (ϖ : Per.Fl l) (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l))
    (hk : Per.kerP l = Ideal.span {beta ϖ}) (i : ℕ) : ∀ c : Per.AinfP l, beta ϖ ^ i * c ∈ Sa ϖ → c ∈ Sa ϖ := by
  induction i with
  | zero => intro c hc; simpa using hc
  | succ i ih =>
    intro c hc
    refine Sa_cancel_beta ϖ hϖ hk c (ih _ ?_)
    rwa [← mul_assoc, ← pow_succ]

theorem Sg_div_betaD_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  intro l _ ϖ hϖ hk hF s hs i hd
  obtain ⟨s₀, hs₀, rfl⟩ := Subring.mem_map.1 hs
  have hβ : beta ϖ ∈ Per.kerP l := by rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : s₀ ∈ Per.kerP l ^ i := by
    obtain ⟨z, hz⟩ := hd
    have hb : betaD ϖ ^ i = algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ ^ i) := by rw [map_pow, betaD]
    have h1 := congrArg (Per.ev l i) hz
    rw [hb, map_mul, GlobalTheory.MemLoc.ev_algebraMap, GlobalTheory.MemLoc.ev_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hβ i), zero_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have hcS : c ∈ Sa ϖ := Sa_cancel_beta_pow ϖ hϖ hk i c (by rw [mul_comm, hc]; exact hs₀)
  refine ⟨algebraMap (Per.AinfP l) (Per.BdRp l) c, Subring.mem_map.2 ⟨c, hcS, rfl⟩, ?_⟩
  rw [← hc, map_mul, map_pow, mul_comm, betaD]

end GlobalTheory.Pst.StLat.BetaDiv
