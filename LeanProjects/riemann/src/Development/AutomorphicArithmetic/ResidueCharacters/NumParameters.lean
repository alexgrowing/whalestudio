import Mathlib
import Formalism.LocalRingCardinality.DataParams

noncomputable section

open NumberField Formalism Formalism.BasicNotions

namespace UpperTheory.N.Num

variable {D : D7}

theorem ranks (D : D7) : (1 : ℝ) ≤ D.R.m ∧ (D.R.m : ℝ) ≤ D.R.f ∧ (D.R.f : ℝ) ≤ D.R.k ∧ (D.R.k : ℝ) ≤ D.R.r ∧
    (D.R.r : ℝ) ≤ D.R.t ∧ (D.R.t : ℝ) ≤ D.R.nV ∧ (D.R.nV : ℝ) ≤ 2 * D.R.t := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h3 := D.R.f_le_k
  have h4 := D.R.rank_add_five_le
  have e1 : D.R.f = 2 * D.R.ord := rfl
  have e2 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e3 : D.R.nV = D.R.r + D.R.t := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_cast <;> omega

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b := Real.one_le_exp (by linarith [one_le_L L])

theorem condN_le (L : SizeData₂ D) (P : ParameterChoice' D L) : (D.host.condN : ℝ) ≤ L.sc.b := by
  have hc := P.condE_le
  have hb := one_le_b L
  obtain ⟨r1, r2, r3, r4, r5, -, -⟩ := ranks D
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ (by linarith)
  have h1 : L.sc.b ^ ((1 : ℝ) / 2) ≤ L.sc.b := by
    conv_rhs => rw [← Real.rpow_one L.sc.b]
    exact Real.rpow_le_rpow_of_exponent_le hb (by norm_num)
  have e : (LevelStarExponents.condE D : ℝ) = D.host.condN := rfl
  rw [e] at hc
  have h2 : (D.host.condN : ℝ) ≤ (D.host.condN : ℝ) ^ 36 := by exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h3 : (D.host.condN : ℝ) ^ 36 ≤ (D.host.condN : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

theorem sizes_le_b (L : SizeData₂ D) (P : ParameterChoice' D L) :
    L.Sc ≤ L.sc.b ∧ L.etaSz ≤ L.sc.b ∧ (D.R.t : ℝ) ≤ L.sc.b := by
  have hb := one_le_b L
  have hL := one_le_L L
  obtain ⟨r1, r2, r3, r4, r5, -, -⟩ := ranks D
  have hη : L.etaSz ≤ L.sc.b := by
    refine P.eta_le.trans (div_le_self (by linarith) ?_)
    have h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 (by linarith)) h2
  refine ⟨?_, hη, P.t_le_eta.trans hη⟩
  have hS := L.Sc_pos
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hden : (D.R.m : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by
    have h1 : (0 : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    have h2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (by linarith)
    have h3 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * ((D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L)) :=
      le_mul_of_one_le_right (by linarith) h2
    rw [← mul_assoc] at h3
    linarith
  have hle : LevelStarExponents.lStar L ≤ L.sc.b := by
    unfold LevelStarExponents.lStar
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < LevelStarExponents.lStar L := by
    unfold LevelStarExponents.lStar
    exact div_pos (by nlinarith) (by linarith)
  have h1 := P.lstar1
  have hb' : 0 < L.sc.b' := by
    have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have h2 : 0 ≤ L.sc.b / LevelStarExponents.lStar L := by positivity
  have h3 := L.etaSz_pos
  linarith

theorem factorization_condN (H : D7) {l : ℕ} (hs : l ∈ H.host.small) :
    H.host.condN.factorization l = H.host.QS.factorization l := by
  have h := Nat.mem_primeFactors.1 hs
  have e : H.host.condN = H.host.QS * (H.host.q * H.host.d) := mul_assoc _ _ _
  rw [e, Nat.factorization_eq_of_coprime_left H.host.QS_coprime (Nat.mem_primeFactorsList'.2 h)]

theorem s0_eq (i : D.nd.Loc) (hs : D.nd.l i ∈ D.host.small) (h2 : D.nd.l i ≠ 2) :
    D.nd.s0 i = max 1 (D.host.condN.factorization (D.nd.l i)) := by
  rw [D.nd.restNLevelExponent_of_odd i h2, factorization_condN D hs]

end UpperTheory.N.Num

end
