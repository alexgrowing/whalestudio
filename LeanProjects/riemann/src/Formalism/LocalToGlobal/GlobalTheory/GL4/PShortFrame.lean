import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTMain
import Formalism.LocalToGlobal.GlobalTheory.GL4.PShortSpan

noncomputable section

open NumberField Module

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem shortSpan_mono (S : HSpace E) (q : ℕ) {ρ ρ' : ℝ} (h : ShortSpan S q ρ) (hle : ρ ≤ ρ') :
    ShortSpan S q ρ' := by
  intro L hL hq
  rw [eq_top_iff, ← h L hL hq]
  exact Submodule.span_mono fun x hx ↦ ⟨hx.1, hx.2.trans hle⟩

theorem shortSpan_of_pos (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (q : ℕ) (hq : q ≠ 0) :
    ShortSpan S q (18 * (S.rank : ℝ) ^ 2 *
      ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (1 / (finrank ℚ E : ℝ)) + 18) := by
  intro L hL hLT
  obtain ⟨r, hr, hspan⟩ := LT.span_trR_short S hσ hsig hpos q hq L hL hLT
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_mono fun x hx ↦ ⟨hx.1, ?_⟩
  set d : ℝ := (finrank ℚ E : ℝ) with hd
  set X : ℝ := (q : ℝ) * ((discr E).natAbs : ℝ) ^ 2 with hXdef
  have hX : 0 < X := by
    have : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
    positivity
  have hd1 : (1 : ℝ) ≤ d := by rw [hd]; exact_mod_cast Module.finrank_pos
  set Y : ℝ := X ^ (1 / d) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hX _
  have hneg : X ^ (-(1 / d)) = Y⁻¹ := Real.rpow_neg hX.le _
  set lam := Real.sqrt (d * X ^ (-(1 / d))) with hlam
  have hlam2 : lam ^ 2 = d / Y := by
    rw [hlam, Real.sq_sqrt (by positivity), hneg, div_eq_mul_inv]
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have hmean : meanAbs (S.hT x x) = LT.trR (S.hT x x) / d := by
    unfold meanAbs LT.trR
    rw [Complex.re_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ ↦ LT.norm_eq_re S hσ hsig hpos σ x
  rw [hmean, div_le_iff₀ (by linarith)]
  refine hx.2.trans ?_
  set t : ℝ := (r : ℝ) / 2 / lam with ht
  have ht0 : 0 ≤ t := by positivity
  have htl : t * lam = (r : ℝ) / 2 := by rw [ht]; field_simp
  have ht2 : t ^ 2 * (d / Y) = (r : ℝ) ^ 2 / 4 := by
    rw [← hlam2, ← mul_pow, htl]; ring
  have hr' : (r : ℝ) ≤ 2 * d * S.rank := by
    have := (Nat.cast_le (α := ℝ)).2 hr
    push_cast at this
    linarith
  have hr2 : (r : ℝ) ^ 2 ≤ 4 * d ^ 2 * (S.rank : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ r := by positivity
    nlinarith
  have ht2' : t ^ 2 ≤ d * (S.rank : ℝ) ^ 2 * Y := by
    have e1 : t ^ 2 = (r : ℝ) ^ 2 * Y / (4 * d) := by
      field_simp at ht2 ⊢
      linarith
    rw [e1, div_le_iff₀ (by positivity)]
    nlinarith
  have hsq : (3 * (t + 1)) ^ 2 ≤ 18 * t ^ 2 + 18 := by nlinarith [sq_nonneg (t - 1)]
  have hn : (0 : ℝ) ≤ (S.rank : ℝ) ^ 2 * Y := by positivity
  calc (3 * ((r : ℝ) / 2 / lam + 1)) ^ 2 = (3 * (t + 1)) ^ 2 := rfl
    _ ≤ 18 * t ^ 2 + 18 := hsq
    _ ≤ 18 * (d * (S.rank : ℝ) ^ 2 * Y) + 18 := by linarith
    _ ≤ (18 * (S.rank : ℝ) ^ 2 * Y + 18) * d := by nlinarith

end Gen

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem disc_rpow (D : D7) :
    (((discr D.host.E).natAbs : ℝ) ^ 2) ^ (1 / (finrank ℚ D.host.E : ℝ)) = (2 * D.host.v) ^ 2 := by
  have h2v : 2 * D.host.v = D.host.rdE := by
    show 2 * (D.host.rdE / 2) = D.host.rdE
    ring
  rw [h2v]
  unfold Formalism.BasicNotions.Host.rdE
  have habs : |(discr D.host.E : ℝ)| = ((discr D.host.E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem T_rpow (D : D7) (u : D.what₂.Word) :
    (((Tu D u ^ (2 * D.R.f) : ℕ) : ℝ)) ^ (1 / (finrank ℚ D.host.E : ℝ)) = (Tu D u : ℝ) := by
  rw [Formalism.MainNotions.flipTwoThree.b_finrank_host]
  push_cast
  have hf : (2 * D.R.f : ℕ) ≠ 0 := by
    have := one_le_f D
    omega
  have := Real.pow_rpow_inv_natCast (x := (Tu D u : ℝ)) (by positivity) hf
  rw [one_div]
  push_cast at this
  exact this

theorem rho_le (D : D7) (u : D.what₂.Word) (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ (Tu D u : ℝ)) :
    18 * (n : ℝ) ^ 2 * (q * (2 * D.host.v) ^ 2) + 18 ≤ msRho D u 90 n := by
  have hv : 1 ≤ D.host.v := one_le_hostv D
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_f D
  have hT : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold msRho radiusSq
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hv2 : (1 : ℝ) ≤ D.host.v ^ 2 := one_le_pow₀ hv
  have hT2 : (Tu D u : ℝ) ≤ (Tu D u : ℝ) ^ 2 := by nlinarith
  have hA : 0 ≤ (n : ℝ) ^ 2 * D.host.v ^ 2 := by positivity
  have h1 : 18 * (n : ℝ) ^ 2 * (q * (2 * D.host.v) ^ 2) ≤ 72 * ((n : ℝ) ^ 2 * D.host.v ^ 2) * (Tu D u : ℝ) ^ 2 := by
    have : q ≤ (Tu D u : ℝ) ^ 2 := hq.trans hT2
    nlinarith
  have h2 : (18 : ℝ) ≤ 18 * ((n : ℝ) ^ 2 * D.host.v ^ 2) * (Tu D u : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 2 * D.host.v ^ 2 := one_le_mul_of_one_le_of_one_le hn2 hv2
    have : (1 : ℝ) ≤ (Tu D u : ℝ) ^ 2 := one_le_pow₀ hT
    nlinarith
  have h3 : 90 * ((n : ℝ) ^ 2 * D.host.v ^ 2) * (Tu D u : ℝ) ^ 2 ≤ 90 * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2 := by
    have : 0 ≤ (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2 := by positivity
    nlinarith
  linarith

theorem shortFrame_record (D : D7) (u : D.what₂.Word) :
    (∀ i ≤ D.R.m, ShortFrame (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msRho D u 90 (D.R.N i))) ∧
    ShortFrame D.sp.X' 1 (msRho D u 90 (D.R.N D.R.m - 1)) := by
  have hT0 : Tu D u ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hT1 : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · refine shortFrame_of_span _ _ _ (shortSpan_mono _ _ (shortSpan_of_pos (D.sp.X i) (host_star D) (D.sp.X_sig i)
      (D7.X_posDef D i hi) (Tu D u ^ (2 * D.R.f)) (pow_ne_zero _ hT0)) ?_)
    have hn : 1 ≤ D.R.N i := by
      have := D.R.k_ge
      unfold Ranks.N
      omega
    rw [D.sp.X_rank i hi, Real.mul_rpow (by positivity) (by positivity), T_rpow, disc_rpow]
    exact rho_le D u _ hn _ (by positivity) le_rfl
  · refine shortFrame_of_span _ _ _ (shortSpan_mono _ _ (shortSpan_of_pos D.sp.X' (host_star D) D.sp.X'_sig
      (D7.X'_posDef D) 1 one_ne_zero) ?_)
    have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    have hn : 1 ≤ D.R.N D.R.m - 1 := by
      rw [hN]
      unfold Ranks.rankX' Ranks.r
      have := D.R.k_ge
      omega
    rw [D.sp.X'_rank, ← hN, Real.mul_rpow (by positivity) (by positivity), disc_rpow]
    simp only [Nat.cast_one, Real.one_rpow]
    exact rho_le D u _ hn 1 zero_le_one hT1

end Record

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
