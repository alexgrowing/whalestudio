import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.PerS

noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section Bound

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem norm_chiT_le (P : Pair K G) (x : G) (σ : K →+* ℂ) : ‖σ (chiT P x)‖ ≤ 1 := by
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    have h := chi_inv_pow P ⟨x, hx⟩
    have h2 : (σ (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by rw [← map_pow, h, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h2 (card_H_pos P).ne').le
  · rw [chiT_of_not_mem P x hx, map_zero, norm_zero]; exact zero_le_one

theorem prod_expand (c c' : G → K) (g' g : G) :
    (∑ x : G, c x • MonoidAlgebra.of K G x) * MonoidAlgebra.of K G g' *
        ((∑ y : G, c' y • MonoidAlgebra.of K G y) * MonoidAlgebra.of K G g) =
      ∑ x : G, ∑ y : G, (c x * c' y) • MonoidAlgebra.of K G (x * g' * (y * g)) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hof : MonoidAlgebra.of K G x * MonoidAlgebra.of K G g' * (MonoidAlgebra.of K G y * MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G (x * g' * (y * g)) := by simp only [map_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hof, mul_comm (c' y) (c x)]

theorem entry_bound (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (g' g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G g' * (epsS P * MonoidAlgebra.of K G g))))‖ ≤
      ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
  have hd : (Module.finrank K (T.W s) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast finrank_le_card (T.tau s) (T.irr s)
  rw [epsS, epsS, prod_expand, map_sum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x y : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      ((chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖ ≤ (Fintype.card G : ℝ) := by
    intro x y
    rw [map_smul, map_smul, Representation.asAlgebraHom_of, smul_eq_mul, map_mul, map_mul, norm_mul, norm_mul]
    have h1 := norm_chiT_le P0 x σ
    have h2 := norm_chiT_le P y σ
    have h3 := norm_trace_tau_le (T.tau s) (x * g' * (y * g)) σ
    calc ‖σ (chiT P0 x)‖ * ‖σ (chiT P y)‖ * ‖σ (LinearMap.trace K (T.W s) ((T.tau s) (x * g' * (y * g))))‖
        ≤ 1 * 1 * (Module.finrank K (T.W s) : ℝ) := by
          gcongr
      _ ≤ _ := by rw [one_mul, one_mul]; exact hd
  calc ∑ x : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (∑ y : G, (chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖
      ≤ ∑ x : G, ∑ y : G, (Fintype.card G : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [map_sum, map_sum, map_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Bound

theorem group_data_exists : GrpData := by
  intro K _ _ G _ _ T P0 P hM1
  refine ⟨eS_mul_eS T, fun s z => eS_central T s z, eps_idem P, fun s => intEl_of_intR _ (intR_card_eS T s),
    fun s => ?_⟩
  obtain ⟨g, g', Γ, hΓ, hdet, b', hb'1, hb'2⟩ := perS T P0 P hM1 s
  refine ⟨fun k => epsS P * MonoidAlgebra.of K G (g k), fun j => epsS P0 * MonoidAlgebra.of K G (g' j), Γ, hdet,
    ?_, fun i => intEl_of_intR _ (intR_mul (intR_epsS P) (intR_of _)),
    fun j => intEl_of_intR _ (intR_mul (intR_epsS P0) (intR_of _)), ?_,
    fun i => (absorb_eps T s P P0 _).symm, fun j => (absorb_eps T s P0 P _).symm, b', hb'1, hb'2⟩
  ·
    intro σ
    set ΓK := Γ.map (algebraMap (𝓞 K) K) with hΓK
    have hdetK : algebraMap (𝓞 K) K Γ.det = ΓK.det := RingHom.map_det _ _
    have hentry : ∀ j k, (InfinitePlace.mk σ).1 (ΓK j k) ≤ ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
      intro j k
      show ‖σ (ΓK j k)‖ ≤ _
      rw [hΓK, Matrix.map_apply, hΓ j k]
      exact entry_bound T s P0 P (g' j) (g k) σ
    have hdl := Matrix.det_le hentry
    rw [Fintype.card_fin] at hdl
    rw [hdetK]
    refine (show ‖σ ΓK.det‖ ≤ _ from hdl).trans ?_
    have hnG : nS T P s ≤ Fintype.card G :=
      (Submodule.finrank_le _).trans (finrank_le_card (T.tau s) (T.irr s))
    have hN : ((nS T P s).factorial * (Fintype.card G ^ 3) ^ (nS T P s) : ℕ) ≤
        Fintype.card G ^ (4 * nS T P s) := by
      calc (nS T P s).factorial * (Fintype.card G ^ 3) ^ (nS T P s)
          ≤ (nS T P s) ^ (nS T P s) * (Fintype.card G ^ 3) ^ (nS T P s) :=
            Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
        _ ≤ (Fintype.card G) ^ (nS T P s) * (Fintype.card G ^ 3) ^ (nS T P s) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnG _)
        _ = Fintype.card G ^ (4 * nS T P s) := by ring
    rw [nsmul_eq_mul]
    exact_mod_cast hN
  ·
    intro i j
    have hmul : epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0 =
        epsS P0 * (MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i))) * eps P0 := by
      simp only [mul_assoc]
    have hτ : (T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0) =
        (T.tau s).asAlgebraHom (algebraMap (𝓞 K) K (Γ j i) • eps P0) := by
      rw [hmul, sandwich (T.tau s) P0 (hM1 s), map_smul, ← mul_assoc, ← hΓ j i]
    calc epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * (eps P0 * eS T s)
        = (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0) * eS T s := by
          simp only [mul_assoc]
      _ = (algebraMap (𝓞 K) K (Γ j i) • eps P0) * eS T s := mul_eS_eq T s _ _ hτ
      _ = algebraMap (𝓞 K) K (Γ j i) • (eps P0 * eS T s) := smul_mul_assoc _ _ _

end PI.Dv.TIW
