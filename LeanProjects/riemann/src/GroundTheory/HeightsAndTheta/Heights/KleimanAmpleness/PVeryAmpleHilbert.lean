import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleHilbertSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSnapperSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenPrimeOfEqFinrank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

namespace VeryAmpleHilbert

theorem exists_slice (Q : MvPolynomial (Fin 2) ℚ) (e : ℕ) (hQ : Q.totalDegree ≤ e) (c : ℚ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ e ∧ p.coeff e = Q.coeff (Finsupp.single 0 e) ∧
      ∀ a : ℚ, p.eval a = MvPolynomial.eval ![a, c] Q := by
  have hdeg : ∀ m ∈ Q.support, m 0 + m 1 ≤ e := fun m hm => by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  refine ⟨∑ m ∈ Q.support, Polynomial.C (Q.coeff m * c ^ m 1) * Polynomial.X ^ m 0, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := hdeg m hm
    omega
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 e)]
    · simp
    · intro m hm hne
      rw [if_neg]
      intro hme
      apply hne
      have := hdeg m hm
      ext i
      fin_cases i
      · simp [hme]
      · simp
        omega
    · intro h
      rw [MvPolynomial.notMem_support_iff.mp h]
      simp
  · intro a
    rw [Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem fwdDiff_iter_eval (p : Polynomial ℚ) (e : ℕ) (hp : p.natDegree ≤ e) (y : ℚ) :
    (fwdDiff 1)^[e] p.eval y = e.factorial * p.coeff e := by
  rcases hp.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rw [Polynomial.leadingCoeff, mul_comm]

theorem sum_subsets_eq_fwdDiff (e : ℕ) (f : ℚ → ℚ) :
    ∑ T : Finset (Fin e), (-1 : ℚ) ^ (e - T.card) * f T.card = (fwdDiff 1)^[e] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun m => (-1 : ℚ) ^ (e - m) * f m), Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_const (Q : SubSystem k x Ω) {n : ℕ} (l : List (Fin n)) (m : ℕ) :
    l.foldl (fun F _ => F.twist Q) (Q.pow m) = Q.pow (m + l.length) := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.length_cons]
    change l.foldl _ (Q.pow (m + 1)) = _
    rw [ih]
    congr 1
    omega

theorem tensorSub_const (Q : SubSystem k x Ω) {n : ℕ} (T : Finset (Fin n)) :
    tensorSub (fun _ : Fin n => Q) T = Q.pow T.card := by
  have h := foldl_twist_const Q ((List.finRange n).filter (· ∈ T)) 0
  rw [zero_add] at h
  unfold tensorSub
  refine h.trans ?_
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

end VeryAmpleHilbert

open VeryAmpleHilbert in

theorem VeryAmpleHilbert.proof (hS : VeryAmpleSnapper.Statement.{u, w}) : VeryAmpleHilbert.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hN
  obtain ⟨hfin, Q, c₀, hdeg, hQ, hQ0⟩ := hS k Ω N x e Nb hZ hN
  have hpow : ∀ n : ℕ, twistMul Nb.toSubSystem n 0 = Nb.toSubSystem.pow n := fun n =>
    SubSystem.twist_twistSys_zero _
  refine ⟨fun n => hpow n ▸ hfin n 0, ?_⟩
  obtain ⟨P, hPdeg, hPe, hPev⟩ := exists_slice Q e hdeg 0
  refine ⟨P, hPdeg, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hZ.relevant
    have hxj : x j ≠ 0 := fun h0 => hj ((mem_primeOf_of_isHomogeneous x
      (MvPolynomial.isHomogeneous_X k j)).mpr (by rw [MvPolynomial.aeval_X, h0]))
    have hsum : ∀ c : ℕ, c₀ ≤ c → (interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c : ℚ) =
        e.factorial * Q.coeff (Finsupp.single 0 e) := by
      intro c hc
      obtain ⟨p, hpd, hpe, hpv⟩ := exists_slice Q e hdeg c
      rw [← hpe, ← fwdDiff_iter_eval p e hpd 0, funext hpv, ← sum_subsets_eq_fwdDiff, interSum]
      push_cast
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [tensorSub_const, SectionsOverLocalization.restrLen_primeOf_eq_finrank x hxj, Int.cast_natCast]
      congr 1
      have h := hQ T.card c hc
      rw [Int.cast_natCast] at h
      exact h
    set z := interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c₀.toNat
    have hz : ∀ c : ℕ, c₀.toNat ≤ c →
        interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c = z := fun c hc => by
      have h1 := hsum c (by omega)
      rw [← hsum c₀.toNat (by omega)] at h1
      exact_mod_cast h1
    have hlim : interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) = z :=
      (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨c₀.toNat, fun c hc => (hz c hc).symm⟩)).limUnder_eq
    rw [hlim, hsum c₀.toNat (by omega), hPe, mul_comm]
  · filter_upwards [hQ0] with n hn
    rw [hn, hPev]

end

end GroundTheory.Heights₂.Heights.Kleiman
