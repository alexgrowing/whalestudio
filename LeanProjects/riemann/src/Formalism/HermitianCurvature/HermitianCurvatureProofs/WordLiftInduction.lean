import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDegreePolynomials

namespace Formalism.FourierDecayAlt.P.WordLiftInduction

open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem top_eq_sum {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (h : IsTopCoeff W d c) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) : ∑ j, ((lagCo y j : ℝ) : ℂ) * W (y j) = c := by
  obtain ⟨P, hd, hc, hP⟩ := h
  have hinj : Function.Injective (fun j => ((y j : ℝ) : ℂ)) :=
    fun a b hab => hy (Complex.ofReal_injective hab)
  have hlt : P.degree < (univ : Finset (Fin (d + 1))).card := by
    rw [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hd)
  have h := Lagrange.coeff_eq_sum (s := univ) (v := fun j => ((y j : ℝ) : ℂ)) hinj.injOn hlt
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h
  rw [← hc, h]
  refine sum_congr rfl fun i _ => ?_
  rw [hP]
  unfold lagCo
  push_cast
  rw [prod_inv_distrib, div_eq_mul_inv, mul_comm]

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Fw_ind (Ξ : Sesq M) (X X' : M) (T : (R → R → ℂ) → Prop)
    (hsub : ∀ Φ Ψ, T Φ → T Ψ → T (fun P P' => Φ P P' - Ψ P P'))
    (hbase : ∀ Q Q' : R, T (fun P P' => Ξ ((P * Q) • X) ((P' * Q') • X'))) :
    ∀ (w : List (Dat R × ℝ)) (Q Q' : R), T (fun P P' => Fw Ξ X X' w (P * Q) (P' * Q')) := by
  intro w
  induction w with
  | nil => intro Q Q'; exact hbase Q Q'
  | cons l w ih =>
    intro Q Q'
    simp only [Fw, mul_assoc]
    exact hsub _ _ (ih _ _) (ih _ _)

def one (Ξ : Sesq M) (D : Dat R) (y : ℝ) (x x' : M) : ℂ :=
  Ξ ((evR D.B y + algebraMap ℂ R D.s * evR D.A y) • x) (evR D.Av (y + 1) • x') -
    Ξ (evR D.A y • x) (evR D.Bv (y + 1) • x')

theorem head_step (Ξ : Sesq M) (X X' : M) {d : ℕ} (D : Dat R) (g : Fin (d + 1) → ℝ) (c : ℂ)
    (h : ∀ Q Q' : R, ∑ i, ((lagCo g i : ℝ) : ℂ) * one Ξ D (g i) (Q • X) (Q' • X') =
      c * Ξ (Q • X) (Q' • X'))
    (w : List (Dat R × ℝ)) :
    ∑ i, ((lagCo g i : ℝ) : ℂ) * Fw Ξ X X' ((D, g i) :: w) 1 1 = c * Fw Ξ X X' w 1 1 := by
  have key := Fw_ind Ξ X X' (fun Φ => ∑ i, ((lagCo g i : ℝ) : ℂ) *
      (Φ (evR D.B (g i) + algebraMap ℂ R D.s * evR D.A (g i)) (evR D.Av (g i + 1)) -
        Φ (evR D.A (g i)) (evR D.Bv (g i + 1))) = c * Φ 1 1) ?_ ?_ w 1 1
  · simpa [Fw] using key
  · intro Φ Ψ hΦ hΨ
    simp only
    rw [mul_sub, ← hΦ, ← hΨ, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  · intro Q Q'
    simpa [one, mul_smul] using h Q Q'

theorem word (Ξ : Sesq M) (d : ℕ) (X X' : M) : ∀ (K : ℕ) (dat : Fin K → Dat R) (c : Fin K → ℂ)
    (grid : Fin K → Fin (d + 1) → ℝ),
    (∀ a (Q Q' : R), ∑ i, ((lagCo (grid a) i : ℝ) : ℂ) *
      one Ξ (dat a) (grid a i) (Q • X) (Q' • X') = c a * Ξ (Q • X) (Q' • X')) →
    (∏ a, c a) * Ξ X X' =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1 := by
  intro K
  induction K with
  | zero =>
    intro dat c grid _
    simp [Fw]
  | succ K ih =>
    intro dat c grid h
    have ih' := ih (fun a => dat a.succ) (fun a => c a.succ) (fun a => grid a.succ)
      (fun a => h a.succ)
    rw [Fin.prod_univ_succ, mul_assoc, ih', mul_sum,
      ← (Fin.consEquiv (fun _ : Fin (K + 1) => Fin (d + 1))).sum_comp, Fintype.sum_prod_type,
      sum_comm]
    refine sum_congr rfl fun j' _ => ?_
    rw [mul_left_comm, ← head_step Ξ X X' (dat 0) (grid 0) (c 0) (h 0), mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ]
    push_cast
    ring

theorem bound (Ξ : Sesq M) (d K : ℕ) (dat : Fin K → Dat R) (c : Fin K → ℂ)
    (grid : Fin K → Fin (d + 1) → ℝ) (X X' : M) (S : Fin K → ℝ) (B : ℝ)
    (hw : (∏ a, c a) * Ξ X X' =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1)
    (hS : ∀ a, ∑ i, |lagCo (grid a) i| = S a)
    (hB : ∀ j : Fin K → Fin (d + 1),
      ‖Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1‖ ≤ B) :
    (∏ a, ‖c a‖) * ‖Ξ X X'‖ ≤ (∏ a, S a) * B := by
  rw [← norm_prod, ← norm_mul, hw]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [← hS]
  rw [prod_univ_sum, sum_mul, Fintype.piFinset_univ]
  refine sum_le_sum fun j _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_prod]
  exact mul_le_mul_of_nonneg_left (hB j) (prod_nonneg fun _ _ => abs_nonneg _)

theorem one_planeWave (Ξ : Sesq M) (n : ℕ) (D : Dat R) (x x' : M) (h : Shape n D.A D.B)
    (hv : Shape n D.Av D.Bv) : IsTopCoeff (fun Y => one Ξ D Y x x') (2 * n) (D.s * Ξ x x') := by
  have h1 := plane_wave_top_degree R M Ξ n D.A D.B D.Av D.Bv D.s x x' h hv
  have hJ : ∀ Y : ℝ, pair2 Ξ (act2 (Formalism.YangianSpanCharacter.T.J R * Formalism.YangianSpanCharacter.T.Uinv (A := R) D.s) (vec D.A D.B Y x))
      (vec D.Av D.Bv (Y + 1) x') = one Ξ D Y x x' :=
    fun Y => j_pairing_formula R M Ξ D.A D.B D.Av D.Bv D.s Y (Y + 1) x x'
  simpa only [hJ] using h1

theorem one_lift (Ξ : Sesq M) (n s : ℕ) (D : Dat R) (A₀ A₀v : R[X]) (e t t' : ℂ) (X X' : M)
    (hs : D.s = 0) (he : e = 1 ∨ e = -1)
    (hA : D.A.Monic ∧ D.A.natDegree = n + s ∧ D.Av.Monic ∧ D.Av.natDegree = n + s)
    (hA₀ : A₀.Monic ∧ A₀.natDegree = n ∧ A₀v.Monic ∧ A₀v.natDegree = n)
    (h1 : ∀ (Y : ℝ) (Q Q' : R), Ξ (evR D.B Y • Q • X) (Q' • X') =
      Ξ ((e * t⁻¹) • evR A₀ Y • Q • X) (Q' • X'))
    (h2 : ∀ (Y : ℝ) (Q Q' : R), Ξ (Q • X) (evR D.Bv Y • Q' • X') =
      Ξ (Q • X) ((e * (starRingEnd ℂ t')⁻¹) • evR A₀v Y • Q' • X'))
    (Q Q' : R) :
    IsTopCoeff (fun Y => one Ξ D Y (Q • X) (Q' • X')) (2 * n + s)
      (e * (1 / t - 1 / t') * Ξ (Q • X) (Q' • X')) := by
  obtain ⟨hAm, hAd, hAvm, hAvd⟩ := hA
  obtain ⟨hA₀m, hA₀d, hA₀vm, hA₀vd⟩ := hA₀
  have p1 := pairing_top_degree R M Ξ A₀ D.Av n (n + s) 1 (Q • X) (Q' • X') hA₀d.le hAvd.le
  have p2 := pairing_top_degree R M Ξ D.A A₀v (n + s) n 1 (Q • X) (Q' • X') hAd.le hA₀vd.le
  have c1 : A₀.coeff n = 1 := by rw [← hA₀d]; exact hA₀m.coeff_natDegree
  have c2 : D.Av.coeff (n + s) = 1 := by rw [← hAvd]; exact hAvm.coeff_natDegree
  have c3 : D.A.coeff (n + s) = 1 := by rw [← hAd]; exact hAm.coeff_natDegree
  have c4 : A₀v.coeff n = 1 := by rw [← hA₀vd]; exact hA₀vm.coeff_natDegree
  rw [c1, c2, one_smul, one_smul, show n + (n + s) = 2 * n + s by ring] at p1
  rw [c3, c4, one_smul, one_smul, show n + s + n = 2 * n + s by ring] at p2
  have hce : starRingEnd ℂ e = e := by
    rcases he with rfl | rfl <;> simp
  have key := TopDegreePolynomials.isTop_sub (TopDegreePolynomials.isTop_const_mul (e * t⁻¹) p1) (TopDegreePolynomials.isTop_const_mul (e * t'⁻¹) p2)
  have hfun : (fun Y : ℝ => one Ξ D Y (Q • X) (Q' • X')) = fun Y : ℝ =>
      e * t⁻¹ * Ξ (evR A₀ Y • Q • X) (evR D.Av (Y + 1) • Q' • X') -
        e * t'⁻¹ * Ξ (evR D.A Y • Q • X) (evR A₀v (Y + 1) • Q' • X') := by
    funext Y
    unfold one
    rw [hs, map_zero, zero_mul, add_zero]
    congr 1
    · rw [← mul_smul (evR D.Av (Y + 1)) Q' X', h1, LinearMap.map_smul Ξ, LinearMap.smul_apply, smul_eq_mul]
    · rw [← mul_smul (evR D.A Y) Q X, h2, LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_inv₀,
        Complex.conj_conj, hce]
  rw [hfun]
  have hc : e * (1 / t - 1 / t') * Ξ (Q • X) (Q' • X') =
      e * t⁻¹ * Ξ (Q • X) (Q' • X') - e * t'⁻¹ * Ξ (Q • X) (Q' • X') := by
    rw [one_div, one_div]; ring
  rw [hc]
  exact key

end

end Formalism.FourierDecayAlt.P.WordLiftInduction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem plane_wave_word_chebyshev_alt : Formalism.FourierDecayAlt.F7.PlaneWaveWordCheb := by
  intro R M _ _ _ _ _ _ Ξ n K dat α β X X' B hn hαβ hsh hB
  have hch := fun a => chebyshev_bound_sharp (α a) (β a) (2 * n) (hαβ a) (by omega)
  exact WordLiftInduction.bound Ξ (2 * n) K dat (fun a => (dat a).s)
    (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) X X' _ B
    (WordLiftInduction.word Ξ (2 * n) X X' K dat _ _ fun a Q Q' =>
      WordLiftInduction.top_eq_sum (WordLiftInduction.one_planeWave Ξ n (dat a) (Q • X) (Q' • X') (hsh a).1 (hsh a).2) _
        (hch a).1)
    (fun a => (hch a).2) hB

theorem lift_word_chebyshev : Formalism.FourierDecayAlt.F7.LiftWordCheb := by
  intro R M _ _ _ _ _ _ Ξ n s K dat A₀ A₀v e t t' α β X X' B hs hs0 he _ hA hA₀ h1 h2 hαβ hB
  have hch := fun a => chebyshev_bound_sharp (α a) (β a) (2 * n + s) (hαβ a) (by omega)
  have hb := WordLiftInduction.bound Ξ (2 * n + s) K dat (fun a => e a * (1 / t a - 1 / t' a))
    (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) X X' _ B
    (WordLiftInduction.word Ξ (2 * n + s) X X' K dat _ _ fun a Q Q' =>
      WordLiftInduction.top_eq_sum (WordLiftInduction.one_lift Ξ n s (dat a) (A₀ a) (A₀v a) (e a) (t a) (t' a) X X' (hs0 a)
        (he a) (hA a) (hA₀ a) (h1 a) (h2 a) Q Q') _ (hch a).1)
    (fun a => (hch a).2) hB
  have hn : ∀ a, ‖e a * (1 / t a - 1 / t' a)‖ = ‖1 / t a - 1 / t' a‖ := by
    intro a
    rw [norm_mul]
    rcases he a with h | h <;> simp [h]
  simpa only [hn] using hb

end Formalism.FourierDecayAlt.P
