import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdealStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.VacMove

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sgA_mem (D : D7) {s : AE D} (hs : s ∈ OhE D) : sgA D s ∈ OhE D :=
  Formalism.UG.P.csDual_sig_mem _ hs

theorem inc_int (D : D7) (b : 𝓞 D.host.E) : inc D (b : D.host.E) ∈ OhE D :=
  (GlobalTheory.NormSum.AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨b, rfl⟩

theorem inc_dvd (D : D7) {N : ℕ} {b : 𝓞 D.host.E} (h : (N : 𝓞 D.host.E) ∣ b) :
    ∃ w ∈ OhE D, inc D (b : D.host.E) = (N : AE D) * w := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨_, inc_int D c, ?_⟩
  rw [← map_natCast (inc D), ← map_mul]
  simp

theorem exists_nat_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D :=
  (GlobalTheory.T.cmFiniteAdele_strong_approx_mod_adelicIdeal D ⊤ top_ne_bot).2.1 y

theorem zeroAt_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ZeroAt D q (x * y) := by
  intro k
  obtain ⟨n, hn, hy⟩ := exists_nat_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

theorem exists_half_idem (D : D7) : ∃ ε ∈ OhE D, ε * ε = ε ∧ ε * sgA D ε = 0 ∧ ∀ q : ℕ, q.Prime →
    (InertQ D q → ZeroAt D q (ε + sgA D ε)) ∧ (¬ InertQ D q → ZeroAt D q (1 - (ε + sgA D ε))) := by
  obtain ⟨e, h1, h2, h3⟩ := GlobalTheory.T.exists_cm_idempotents_select_conjugate_primes D
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.T.cmFiniteAdele_integral_separated_complete D
  have hc : ∀ b : 𝓞 D.host.E, inc D ((D.host.conj • b : 𝓞 D.host.E) : D.host.E) = sgA D (inc D b) := by
    intro b
    rw [GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  obtain ⟨ε, hε, h⟩ := hcpl (fun N => inc D (e N : D.host.E)) (fun N => inc_int D _) (by
    intro N m hN hm
    obtain ⟨w, hw, h⟩ := inc_dvd D (h1 N m hN hm)
    refine ⟨w, hw, ?_⟩
    rw [← h]; simp)
  refine ⟨ε, hε, ?_, ?_, fun q hq => ⟨fun hi k => ?_, fun hi k => ?_⟩⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨v, hv, hh'⟩ := inc_dvd D (h2 N hN).1
    have hh'' : inc D (e N : D.host.E) * inc D (e N : D.host.E) - inc D (e N : D.host.E) = N * v := by
      rw [← hh']; simp
    refine ⟨v + (2 * inc D (e N : D.host.E) * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem hv (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (inc_int D _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [hh]; linear_combination hh''
  · refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨v, hv, hh'⟩ := inc_dvd D (h2 N hN).2
    have hh'' : inc D (e N : D.host.E) * sgA D (inc D (e N : D.host.E)) = N * v := by
      rw [← hh', ← hc]; simp
    refine ⟨v + (inc D (e N : D.host.E) * sgA D w + w * sgA D (inc D (e N : D.host.E)) + N * w * sgA D w), ?_, ?_⟩
    · exact add_mem hv (add_mem (add_mem (mul_mem (inc_int D _) (sgA_mem D hw))
        (mul_mem hw (sgA_mem D (inc_int D _)))) (mul_mem (mul_mem (natCast_mem _ _) hw) (sgA_mem D hw)))
    · rw [hh, map_add, map_mul, map_natCast]; linear_combination hh''
  · obtain ⟨w, hw, hh⟩ := h (q ^ k) (pow_pos hq.pos k)
    obtain ⟨v, hv, hh'⟩ := inc_dvd D ((h3 q k hq).1 hi)
    have hh'' : inc D (e (q ^ k) : D.host.E) + sgA D (inc D (e (q ^ k) : D.host.E)) = (q ^ k : ℕ) * v := by
      rw [← hh', ← hc]; simp
    refine ⟨1, one_pos, by simp, v + (w + sgA D w), add_mem hv (add_mem hw (sgA_mem D hw)), ?_⟩
    rw [hh, map_add, map_mul, map_natCast]
    push_cast at hh'' ⊢
    linear_combination hh''
  · obtain ⟨w, hw, hh⟩ := h (q ^ k) (pow_pos hq.pos k)
    obtain ⟨v, hv, hh'⟩ := inc_dvd D ((h3 q k hq).2 hi)
    have hh'' : 1 - (inc D (e (q ^ k) : D.host.E) + sgA D (inc D (e (q ^ k) : D.host.E))) = (q ^ k : ℕ) * v := by
      rw [← hh', ← hc]; simp
    refine ⟨1, one_pos, by simp, v - (w + sgA D w), sub_mem hv (add_mem hw (sgA_mem D hw)), ?_⟩
    rw [hh, map_add, map_mul, map_natCast]
    push_cast at hh'' ⊢
    linear_combination hh''

theorem exists_splitComp (D : D7) (u : (AE D)ˣ) (hu : (u : AE D) * sgA D u = 1) :
    ∃ z x : (AE D)ˣ, SplitComp D u z ∧ x = z * sgU D x ∧ ((u : AE D) ∈ OhE D → IntU D x) := by
  obtain ⟨ε, hε, h1, h2, h3⟩ := exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  set η := sgA D ε with hη
  set v := sgA D u with hv
  have hz : ((1 - (ε + η)) + (ε + η) * u) * ((1 - (ε + η)) + (ε + η) * v) = 1 := by
    linear_combination (1 - u - v + u * v) * (h1 + h1' + 2 * h2) + (ε + η) * hu
  have hx : ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
    linear_combination (1 - u - v + u * v) * h1' + η * hu
  refine ⟨⟨_, _, hz, by rw [mul_comm, hz]⟩, ⟨_, _, hx, by rw [mul_comm, hx]⟩, fun q hq => ⟨fun hi => ?_, fun hi => ?_⟩,
    ?_, fun hO => ⟨?_, ?_⟩⟩
  · convert zeroAt_mul D hq ((h3 q hq).1 hi) (u - 1) using 1
    simp only; ring
  · convert zeroAt_mul D hq ((h3 q hq).2 hi) (1 - u) using 1
    simp only; ring
  · ext
    change (1 - η) + η * u = ((1 - (ε + η)) + (ε + η) * u) * sgA D ((1 - η) + η * u)
    rw [map_add, map_mul, map_sub, map_one, hη, sgA_sgA, ← hη, ← hv]
    linear_combination (-(1 - u - v + u * v)) * (h1 + h2) - ε * hu
  · exact add_mem (sub_mem (one_mem _) (sgA_mem D hε)) (mul_mem (sgA_mem D hε) hO)
  · exact add_mem (sub_mem (one_mem _) (sgA_mem D hε)) (mul_mem (sgA_mem D hε) (sgA_mem D hO))

theorem det_norm (D : D7) {N : ℕ} (g : GA D N) :
    ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) *
      sgA D ((Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) = 1 := by
  have h := congrArg Matrix.det ((GlobalTheory.NormSum.PtsMem.mem_GA D _).1 g.2)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, mul_comm]
  exact h

theorem det_int (D : D7) {N : ℕ} (g : GL (Fin N) (AE D)) (hg : IntG D g) :
    ((Matrix.GeneralLinearGroup.det g : (AE D)ˣ) : AE D) ∈ OhE D := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => (hg _ _).1)

end GlobalTheory.NormSum.VacMove
