import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.VnuMapZero

noncomputable section

open Matrix Classical Finset PI.IsoInvMetric Polynomial

namespace PI.IsoInvMetricW

theorem poly_eq_zero_of_circle (P : ℂ[X]) (h : ∀ z : ℂ, ‖z‖ = 1 → P.eval z = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Set.InjOn (fun t : ℝ => Complex.exp (t * Complex.I)) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    have hpi := Real.pi_gt_three
    have := Complex.exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ hab
    · simpa using this
    all_goals simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero]
    all_goals linarith [ha.1, ha.2, hb.1, hb.2]
  refine ((Set.Ioo_infinite (by norm_num : (0:ℝ) < 1)).image hinj).mono ?_
  rintro _ ⟨t, -, rfl⟩
  exact h _ (Complex.norm_exp_ofReal_mul_I t)

theorem star_mul_self_of_norm {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  have h := Complex.conj_mul' z
  rw [hz] at h
  simpa using h

theorem emb_ge {h N : ℕ} (J : Fin h ↪o Fin N) (i : Fin h) : (i : ℕ) ≤ J i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 : J ⟨n, by omega⟩ < J ⟨n + 1, hi⟩ := J.lt_iff_lt.mpr (by simp [Fin.lt_def])
    have h3 : ((J ⟨n, by omega⟩ : Fin N) : ℕ) < ((J ⟨n + 1, hi⟩ : Fin N) : ℕ) := h2
    simp only at h1 ⊢
    omega

section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

def wt (J : ColChoice N nu) : ℕ := ∑ s, ∑ c, ∑ i, (N - ((J s c i : Fin N) : ℕ))

theorem column_index_val (hle : ∀ z, (nu z).colLen 0 ≤ N) (s : Lt) (c : Fin ((nu s).rowLen 0))
    (i : Fin ((nu s).colLen c)) : ((J0 nu hle s c i : Fin N) : ℕ) = i := by
  simp [J0]

theorem wt_lt (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) (hJ : J ≠ J0 nu hle) :
    wt J < wt (J0 nu hle) := by
  have hex : ∃ s c i, J s c i ≠ J0 nu hle s c i := by
    by_contra hc
    push Not at hc
    apply hJ
    funext s c
    exact DFunLike.ext _ _ (hc s c)
  obtain ⟨s0, c0, i0, h0⟩ := hex
  have hv : ((J s0 c0 i0 : Fin N) : ℕ) ≠ i0 := by
    intro e; apply h0; apply Fin.ext; rw [e, column_index_val]
  have hterm : ∀ s c i, N - ((J s c i : Fin N) : ℕ) ≤ N - ((J0 nu hle s c i : Fin N) : ℕ) := by
    intro s c i; rw [column_index_val]; have := emb_ge (J s c) i; omega
  unfold wt
  apply Finset.sum_lt_sum (fun s _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun i _ => hterm s c i)
  refine ⟨s0, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun c _ => Finset.sum_le_sum fun i _ => hterm s0 c i)
  refine ⟨c0, Finset.mem_univ _, ?_⟩
  apply Finset.sum_lt_sum (fun i _ => hterm s0 c0 i)
  refine ⟨i0, Finset.mem_univ _, ?_⟩
  rw [column_index_val]
  have := emb_ge (J s0 c0) i0
  have := (J s0 c0 i0).isLt
  omega

def dz (z : ℂ) (_s : Lt) (a : Fin N) : ℂ := z ^ (N - (a : ℕ))

theorem vnuMap_torus (z : ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu (fun s => Matrix.diagonal (dz z s)) φ I = z ^ wt I * φ I := by
  rw [vnuMap_eq]
  simp_rw [metric_diagonal Lt N nu (dz z), ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, dz, wt]
  simp_rw [Finset.prod_pow_eq_pow_sum]

theorem torus_unitary {z : ℂ} (hz : ‖z‖ = 1) (s : Lt) :
    Matrix.diagonal (dz (N := N) z s) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp only [dz, Pi.star_apply, star_pow]
  rw [← mul_pow, star_mul_self_of_norm hz, one_pow]

end

theorem hermitian_weight : HW := by
  intro Lt _ _ N nu ip hip ψ hψ
  by_cases hle : ∀ z, (nu z).colLen 0 ≤ N
  · set J0' := J0 nu hle with hJ0'
    set m0 := wt J0' with hm0
    have hu0 : u0 N nu = fun J => if J = J0' then 1 else 0 := by
      funext J; exact unitVector_val_eq nu hle J
    have hu0V : u0 N nu ∈ Vnu N nu := Submodule.subset_span ⟨_, rfl⟩

    set a : ColChoice N nu → ℂ := fun J => ip (u0 N nu) (fun j => if J = j then 1 else 0) with ha
    have hexp : ∀ φ : LaC N nu, ip (u0 N nu) φ = ∑ J, φ J * a J := by
      intro φ
      rw [LinearMap.pi_apply_eq_sum_univ (ip (u0 N nu)) φ]
      rfl
    have hnorm : ip (u0 N nu) (u0 N nu) = 1 := (hip (fun _ => 1) (fun _ => one_mem _)).2
    have haJ0 : a J0' = 1 := by
      have e : (fun j => if J0' = j then (1:ℂ) else 0) = u0 N nu := by
        rw [hu0]; funext j; simp only [eq_comm]
      show ip (u0 N nu) (fun j => if J0' = j then 1 else 0) = 1
      rw [e, hnorm]

    have htor : ∀ z : ℂ, ‖z‖ = 1 →
        ∑ J, z ^ wt J * (ψ J * a J) = z ^ m0 * ∑ J, ψ J * a J := by
      intro z hz
      have hk := (hip (fun s => Matrix.diagonal (dz z s)) (fun s => torus_unitary hz s)).1
        (u0 N nu) hu0V ψ hψ
      have hρu0 : VnuMap nu (fun s => Matrix.diagonal (dz z s)) (u0 N nu) = z ^ m0 • u0 N nu := by
        funext I
        rw [vnuMap_torus, hu0]
        by_cases hI : I = J0'
        · subst hI; simp [hm0]
        · simp [hI]
      rw [hρu0, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hexp, hexp] at hk
      have hzz : z ^ m0 * starRingEnd ℂ (z ^ m0) = 1 := by
        rw [mul_comm]; exact star_mul_self_of_norm (by rw [norm_pow, hz, one_pow])
      calc ∑ J, z ^ wt J * (ψ J * a J)
          = z ^ m0 * (starRingEnd ℂ (z ^ m0) • ∑ J, VnuMap nu (fun s => Matrix.diagonal (dz z s)) ψ J * a J) := by
            rw [smul_eq_mul, ← mul_assoc, hzz, one_mul]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [vnuMap_torus]; ring
        _ = z ^ m0 * ∑ J, ψ J * a J := by rw [hk]

    set S := ∑ J, ψ J * a J with hS
    set P : ℂ[X] := (∑ J, C (ψ J * a J) * X ^ wt J) - C S * X ^ m0 with hP
    have hP0 : P = 0 := by
      apply poly_eq_zero_of_circle
      intro z hz
      rw [hP, eval_sub, eval_finsetSum]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      rw [sub_eq_zero, mul_comm S, ← htor z hz]
      exact Finset.sum_congr rfl fun J _ => by ring
    have hc := congrArg (fun Q : ℂ[X] => Q.coeff m0) hP0
    simp only [hP, coeff_sub, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero, if_true] at hc
    rw [Finset.sum_eq_single J0' (fun J _ hJ => by
        have := wt_lt hle J hJ
        rw [if_neg (by rw [← hm0] at this; omega)]) (fun h => absurd (Finset.mem_univ _) h)] at hc
    rw [if_pos rfl, haJ0, mul_one, sub_eq_zero] at hc
    rw [hexp, ← hS, ← hc]
    simp only [ipl, hu0]
    rw [Finset.sum_eq_single J0' (fun J _ hJ => by simp [hJ]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · push Not at hle
    obtain ⟨z, hz⟩ := hle
    have hrow : 0 < (nu z).rowLen 0 := by
      have hmem : ((0 : ℕ), (0 : ℕ)) ∈ nu z := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
      exact YoungDiagram.mem_iff_lt_rowLen.mp hmem
    have : IsEmpty (ColChoice N nu) := ⟨fun J => by
      have e := J z ⟨0, hrow⟩
      have := Fintype.card_le_of_injective e e.injective
      simp only [Fintype.card_fin] at this
      omega⟩
    have hz0 : u0 N nu = 0 := funext fun J => isEmptyElim J
    rw [hz0]
    simp [ipl]

end PI.IsoInvMetricW
