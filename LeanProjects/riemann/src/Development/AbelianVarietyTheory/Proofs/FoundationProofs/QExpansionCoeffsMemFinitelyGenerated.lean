import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansionsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def clearCoeff (n M w : ℕ) (c : Fin n → Polynomial ℂ) (i : ℕ) (τ : ℍ) : ℂ :=
  if h : i < n then
    DD τ ^ (w * (n - i)) * ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k))
  else DD τ ^ M

theorem dd_pow_mul_eval_jT (p : Polynomial ℂ) (M : ℕ) (hp : p.natDegree ≤ M) (τ : ℍ) :
    DD τ ^ M * p.eval (jT τ) =
      ∑ k ∈ Finset.range (M + 1), p.coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hD := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have hsplit : DD τ ^ M = DD τ ^ (M - k) * DD τ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hsplit]
  simp only [ReciprocityTheory.ChartRestriction.L1.jT, ReciprocityTheory.ChartRestriction.L1.AA]
  rw [div_pow, pow_mul]
  field_simp

theorem sum_clearCoeff_eq_zero (n M w : ℕ) (c : Fin n → Polynomial ℂ) (hM : ∀ i, (c i).natDegree ≤ M)
    (f : ℍ → ℂ) (h : ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0) (τ : ℍ) :
    ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i = 0 := by
  have key : ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i =
      DD τ ^ (w * n + M) * (f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range (fun i => clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i),
      mul_add, Finset.mul_sum, add_comm]
    congr 1
    · simp only [clearCoeff, lt_irrefl, dite_false]
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [clearCoeff, Fin.is_lt, dite_true, Fin.eta]
      rw [← dd_pow_mul_eval_jT _ M (hM i), mul_pow, ← pow_mul]
      have e : w * (n - i) + M + w * i = w * n + M := by
        rw [add_right_comm, ← mul_add, Nat.sub_add_cancel i.isLt.le]
      rw [← e, pow_add, pow_add]
      ring
  rw [key, h τ, mul_zero]

theorem qall_clearCoeff (R : Subring ℂ) (N : ℕ) (hN : 0 < N) (n M w : ℕ) (c : Fin n → Polynomial ℂ)
    (hc : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R) (i : ℕ) :
    QAll (· ∈ R) N (clearCoeff n M w c i) := by
  obtain ⟨hcst, -, -, hmul, hpow, hsum⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hDD : QAll (· ∈ R) N DD := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN DD (Or.inr (Or.inr rfl))).2.1) R
  have hE : QAll (· ∈ R) N ⇑E₄ := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN ⇑E₄ (Or.inl rfl)).2.1) R
  by_cases h : i < n
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ (w * (n - i)) *
        ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
      funext τ; simp [clearCoeff, h]
    rw [hf]
    refine hmul _ _ (hpow _ _ hDD) ?_
    refine (hsum ℕ (Finset.range (M + 1)) _ fun k hk => ?_).1
    exact hmul _ _ (hcst _ (hc _ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
      (hmul _ _ (hpow _ _ hE) (hpow _ _ hDD))
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff, h]
    rw [hf]
    exact hpow _ _ hDD

theorem powerSeries_map_mk {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (g : ℕ → Ω) :
    PowerSeries.map ε (PowerSeries.mk g) = PowerSeries.mk fun k => ε (g k) := by
  ext k; simp [PowerSeries.coeff_map]

theorem qcoeff_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω),
    0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) →
      ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε N w f a hN hLv hF
  classical
  haveI : CharZero Ω := ε.charZero
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range f ⟨N, w, hN, hLv⟩
  set M := ∑ i, (c i).natDegree with hMdef
  have hM : ∀ i, (c i).natDegree ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => (c i).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpre : ∀ (i : Fin n) (k : ℕ), ∃ x : Ω, ε x = (c i).coeff k := fun i k => RingHom.mem_range.1 (hc i k)
  choose e he using hpre
  set S₀ : Finset Ω := Finset.univ.image (fun p : Fin n × Fin (M + 1) => e p.1 p.2) with hS₀
  set A : Subring Ω := Subring.closure (S₀ : Set Ω) with hA
  set R : Subring ℂ := A.map ε with hR
  have hcR : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R := fun i k hk =>
    Subring.mem_map.2 ⟨e i k, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(i, ⟨k, Nat.lt_succ_of_le hk⟩), Finset.mem_univ _, rfl⟩)), he i k⟩
  have hP : ∀ i, QAll (· ∈ R) N (clearCoeff n M w c i) := qall_clearCoeff R N hN n M w c hcR
  choose c' hc'Q hc'R using hP
  have hser := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n (fun τ => DD τ ^ w * f τ) (fun k => ε (a k)) (clearCoeff n M w c) c' hN hF hc'Q
    (sum_clearCoeff_eq_zero n M w c hM f hrel)
  have hpre2 : ∀ i k, ∃ x ∈ A, ε x = c' i k := fun i k => Subring.mem_map.1 (hc'R i k)
  choose d hdA hd using hpre2
  set Q : Polynomial (PowerSeries Ω) :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (d i)) with hQdef
  have hmap : PowerSeries.map ε (Q.eval (PowerSeries.mk a)) =
      (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c' i))).eval
        (PowerSeries.mk fun k => ε (a k)) := by
    simp only [hQdef, Polynomial.eval_finset_sum, Polynomial.eval_monomial, map_sum, map_mul, map_pow,
      powerSeries_map_mk, hd]
  rw [hser] at hmap
  have hQ : Q.eval (PowerSeries.mk a) = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff k) hmap
    simpa [PowerSeries.coeff_map] using this
  have hcoef : ∀ i, Q.coeff i = if i ∈ Finset.range (n + 1) then PowerSeries.mk (d i) else 0 := fun i => by
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    exact Finset.sum_ite_eq' _ _ _
  have hQne : Q ≠ 0 := by
    intro h0
    have hn := hcoef n
    rw [h0, Polynomial.coeff_zero, if_pos (Finset.self_mem_range_succ n)] at hn
    have hc0 : c' n = 0 := funext fun k => by
      have h1 := congrArg (PowerSeries.coeff k) hn
      rw [PowerSeries.coeff_mk, map_zero] at h1
      rw [← hd n k, ← h1, map_zero]; rfl
    have hq := hc'Q n
    have hPn : clearCoeff n M w c n = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff]
    rw [hPn, hc0] at hq
    have hz : HasQ N (fun _ : ℍ => (0 : ℂ)) (0 : ℕ → ℂ) := fun τ => by simpa using hasSum_zero
    have := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N _ _ 0 hq hz
    exact pow_ne_zero M (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero UpperHalfPlane.I) (congrFun this UpperHalfPlane.I)
  have hcA : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A := fun i k => by
    rw [hcoef i]
    split_ifs
    · rw [PowerSeries.coeff_mk]; exact hdA i k
    · simp
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.eisenstein_algebraic_powerSeries_coeff_closure Ω A (PowerSeries.mk a) Q hQne hcA hQ
  refine ⟨S₀ ∪ S₁, fun k => ?_⟩
  have hk := hS₁ k
  rw [PowerSeries.coeff_mk] at hk
  refine (Subring.closure_le.2 ?_) hk
  rintro x (hx | hx)
  · exact Subring.closure_mono (by simp [Finset.coe_union]) hx
  · exact Subring.subset_closure (by simp [hx])

end GlobalTheory.FN
