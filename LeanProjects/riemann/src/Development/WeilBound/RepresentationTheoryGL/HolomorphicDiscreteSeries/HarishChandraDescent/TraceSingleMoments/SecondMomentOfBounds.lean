import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Restrict
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.UnitaryDecomposition PositivityTheory.RgHe

namespace Mom2Aux

theorem block_embed_single {n : ℕ} (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (a b : Fin n) :
    blk0 e (Matrix.single a b (1 : ℂ)) = Matrix.single (e (Sum.inl a)) (e (Sum.inl b)) 1 := by
  ext i j
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  rcases i' with i' | u <;> rcases j' with j' | u' <;>
    simp [blk0, Matrix.single_apply, fromBlocks, e.injective.eq_iff]

theorem trace_dg {m : ℕ} (d : Fin m → ℝ) (X : Matrix (Fin m) (Fin m) ℂ) :
    trace (dg d * X) = ∑ c, X c c * ((d c : ℝ) : ℂ) := by
  simp [Matrix.trace, dg, Matrix.diagonal_mul, mul_comm]

theorem trace_dg_single {m : ℕ} (d : Fin m → ℝ) (a b : Fin m) :
    trace (dg d * Matrix.single a b (1 : ℂ)) = if a = b then ((d a : ℝ) : ℂ) else 0 := by
  rw [trace_dg]
  by_cases h : a = b
  · subst h
    simp [Matrix.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [Matrix.single_apply, if_neg, zero_mul]
    rintro ⟨rfl, rfl⟩
    exact h rfl

theorem casValK_lowK {m : ℕ} (ε : Fin m → Bool) (μ : Fin m → ℝ) :
    casValK ε (lowK ε μ) - casVal μ = 2 * dot μ (rhoN ε) + nsq (rhoN ε) - nsq (rhoC ε) + nsq (rho m) := by
  simp only [casValK, lowK, casVal, nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring)

theorem dot_add_smul {m : ℕ} (x y z : Fin m → ℝ) (t : ℝ) : dot (x + t • y) z = dot x z + t * dot y z := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

end Mom2Aux

private theorem actM_single_lemma {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : Fin m → Fin m → Module.End ℂ M) (p q : Fin m) :
    actM E (Matrix.single p q (1 : ℂ)) = E p q := by
  simp [actM, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq]

private theorem conj_lemma_2 {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) (Z : Matrix (Fin n) (Fin n) ℂ) :
    um g * (um g⁻¹ * Z * um g) * (um g)⁻¹ = Z := by
  have hi : (um g)⁻¹ = um g⁻¹ := (Matrix.coe_units_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).symm
  have h1 : um g * um g⁻¹ = 1 := Units.mul_inv (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  rw [hi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

set_option maxHeartbeats 1600000 in
open Mom2Aux in
theorem second_moment_of_bounds : RootBd → MatBd → AdEq → Mom2 := by
  intro hRoot hMat hAd n ε e lam d d' g hOver
  obtain ⟨L, hL⟩ : ∃ L : Fin (n + 1) → ℝ, ∀ c, L c = lam c + rhoN ε c - rhoC ε c := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin n → Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ a b, Y a b = um g⁻¹ * blk0 e (Matrix.single a b 1) * um g := ⟨_, fun _ _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin n → Fin n → ℝ, ∀ a b, S a b = ∑ i, ∑ j, ‖Y a b i j‖ := ⟨_, fun _ _ => rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Fin n → Fin n → ℝ, ∀ a b, S' a b = ∑ c, ‖Y a b c c‖ * |L c| :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (∑ a, ∑ b, |L a - L b|)
      + |2 * dot lam (rhoN ε) + nsq (rhoN ε) - nsq (rhoC ε) + nsq (rho (n + 1))| := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (∑ a, ∑ b, |d a - d b|) + |2 * dot d (rhoN ε)| := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    exact add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
  have hcab0 : 0 ≤ ∑ a, ∑ b, (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (mul_nonneg (by positivity) (add_nonneg hP0 hQ0)) (by positivity)
  refine ⟨1 + ∑ a, ∑ b, (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2), by linarith, ?_⟩
  intro t ht H _ _ _ π hπ v hv1 hKHW hcas
  have hDer := isDerivedOn_smE hπ
  have hGl := hDer.glRep
  have hIU := isInfUnitary_of_isDerivedOn hπ hDer
  obtain ⟨T', hT'1, hT'2⟩ := hAd (n + 1) ε H π hπ (um g) g.2
  have hTn : ∀ x, ‖T' x‖ = ‖x‖ := by
    intro x
    show ‖(T' x : H)‖ = ‖(x : H)‖
    rw [hT'1]
    exact hπ.2.1 _ g.2 _
  have ht0 : 0 < t := by linarith
  have hΛ : ∀ c, lowK ε (lam + t • d) c = L c + t * d c := by
    intro c
    rw [hL]
    simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcasb : |casValK ε (lowK ε (lam + t • d)) - casVal (lam + t • d)|
      ≤ |2 * dot lam (rhoN ε) + nsq (rhoN ε) - nsq (rhoC ε) + nsq (rho (n + 1))| + t * |2 * dot d (rhoN ε)| := by
    rw [casValK_lowK, dot_add_smul]
    have e1 : 2 * (dot lam (rhoN ε) + t * dot d (rhoN ε)) + nsq (rhoN ε) - nsq (rhoC ε) + nsq (rho (n + 1))
        = (2 * dot lam (rhoN ε) + nsq (rhoN ε) - nsq (rhoC ε) + nsq (rho (n + 1))) + t * (2 * dot d (rhoN ε)) := by
      ring
    rw [e1]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_pos ht0]
  have hR0 : 0 ≤ P + Q * t := add_nonneg hP0 (mul_nonneg hQ0 ht0.le)
  have hoff : ∀ a b, a ≠ b → ‖smE ε π a b v‖ ≤ Real.sqrt (P + Q * t) * ‖v‖ := by
    intro a b hab
    have h1 := hRoot (n + 1) ε _ (smE ε π) hGl hIU (lowK ε (lam + t • d)) _ v hKHW hcas a b hab
    rw [hv1, one_pow, mul_one] at h1
    rw [hv1, mul_one]
    have hLab : |L a - L b| ≤ ∑ a, ∑ b, |L a - L b| :=
      (Finset.single_le_sum (f := fun b' => |L a - L b'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun a' => ∑ b', |L a' - L b'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a))
    have hdab : |d a - d b| ≤ ∑ a, ∑ b, |d a - d b| :=
      (Finset.single_le_sum (f := fun b' => |d a - d b'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)).trans
        (Finset.single_le_sum (f := fun a' => ∑ b', |d a' - d b'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a))
    have hΛab : |lowK ε (lam + t • d) a - lowK ε (lam + t • d) b| ≤ |L a - L b| + t * |d a - d b| := by
      rw [hΛ, hΛ]
      have e2 : L a + t * d a - (L b + t * d b) = (L a - L b) + t * (d a - d b) := by ring
      rw [e2]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_of_pos ht0]
    have htd : t * |d a - d b| ≤ t * ∑ a, ∑ b, |d a - d b| := mul_le_mul_of_nonneg_left hdab ht0.le
    have htq : t * |2 * dot d (rhoN ε)| + t * ∑ a, ∑ b, |d a - d b| = Q * t := by rw [hQ]; ring
    have h2 : ‖smE ε π a b v‖ ^ 2 ≤ P + Q * t := by
      rw [hP]
      linarith
    have h3 := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3
  have hmat := hMat (n + 1) ε _ (smE ε π) hGl hIU (lowK ε (lam + t • d)) (Real.sqrt (P + Q * t)) v hKHW.1
    (Real.sqrt_nonneg _) hoff
  have hab : ∀ a b, ‖smE ε π (e (Sum.inl a)) (e (Sum.inl b)) (T' v)
      - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • T' v‖ ^ 2
      ≤ t * (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2) := by
    intro a b
    have hE : smE ε π (e (Sum.inl a)) (e (Sum.inl b)) = actM (smE ε π) (um g * Y a b * (um g)⁻¹) := by
      rw [hY, conj_lemma_2, block_embed_single, actM_single_lemma]
    have htr : ∑ c, Y a b c c * ((d c : ℝ) : ℂ) = if a = b then ((d' a : ℝ) : ℂ) else 0 := by
      rw [← trace_dg, hY, show (dg d * (um g⁻¹ * blk0 e (Matrix.single a b 1) * um g)).trace
        = (dg d' * Matrix.single a b 1).trace from hOver _, trace_dg_single]
    have hsum : (∑ c, Y a b c c * ((lowK ε (lam + t • d) c : ℝ) : ℂ))
        - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) = ∑ c, Y a b c c * ((L c : ℝ) : ℂ) := by
      simp only [hΛ]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      have e3 : ∑ c, Y a b c c * ((t : ℂ) * (d c : ℂ)) = (t : ℂ) * ∑ c, Y a b c c * (d c : ℂ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [e3, htr]
      split_ifs <;> push_cast <;> ring
    have hdecomp : smE ε π (e (Sum.inl a)) (e (Sum.inl b)) (T' v)
        - (if a = b then ((t * d' a : ℝ) : ℂ) else 0) • T' v
        = T' ((actM (smE ε π) (Y a b) v - (∑ c, Y a b c c * ((lowK ε (lam + t • d) c : ℝ) : ℂ)) • v)
          + (∑ c, Y a b c c * ((L c : ℝ) : ℂ)) • v) := by
      rw [hE, ← hT'2, ← hsum]
      simp only [map_add, map_sub, map_smul, sub_smul]
      abel
    rw [hdecomp, hTn]
    have hn1 := norm_add_le (actM (smE ε π) (Y a b) v - (∑ c, Y a b c c * ((lowK ε (lam + t • d) c : ℝ) : ℂ)) • v)
      ((∑ c, Y a b c c * ((L c : ℝ) : ℂ)) • v)
    have hm := hmat (Y a b)
    rw [hv1, mul_one, ← hS] at hm
    have hs' : ‖(∑ c, Y a b c c * ((L c : ℝ) : ℂ)) • v‖ ≤ S' a b := by
      rw [norm_smul, hv1, mul_one, hS']
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hz0 := norm_nonneg ((actM (smE ε π) (Y a b) v - (∑ c, Y a b c c * ((lowK ε (lam + t • d) c : ℝ) : ℂ)) • v)
          + (∑ c, Y a b c c * ((L c : ℝ) : ℂ)) • v)
    have hz : ‖(actM (smE ε π) (Y a b) v - (∑ c, Y a b c c * ((lowK ε (lam + t • d) c : ℝ) : ℂ)) • v)
          + (∑ c, Y a b c c * ((L c : ℝ) : ℂ)) • v‖ ≤ S a b * Real.sqrt (P + Q * t) + S' a b := by
      linarith
    have hsq := Real.sq_sqrt hR0
    have hS0 : 0 ≤ S a b := by
      rw [hS]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsqrt0 := Real.sqrt_nonneg (P + Q * t)
    have hRt : P + Q * t ≤ t * (P + Q) := by nlinarith
    have k1 : 2 * S a b ^ 2 * (P + Q * t) ≤ 2 * S a b ^ 2 * (t * (P + Q)) :=
      mul_le_mul_of_nonneg_left hRt (by positivity)
    have k2 : 2 * S' a b ^ 2 ≤ t * (2 * S' a b ^ 2) := le_mul_of_one_le_left (by positivity) ht
    calc _ ≤ (S a b * Real.sqrt (P + Q * t) + S' a b) ^ 2 := pow_le_pow_left₀ hz0 hz 2
      _ ≤ 2 * S a b ^ 2 * (P + Q * t) + 2 * S' a b ^ 2 := by
          nlinarith [sq_nonneg (S a b * Real.sqrt (P + Q * t) - S' a b)]
      _ ≤ t * (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2) := by linarith
  refine ⟨T' v, by rw [hTn, hv1], ?_⟩
  calc _ ≤ ∑ a, ∑ b, t * (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hab a b
    _ = t * ∑ a, ∑ b, (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2) := by simp only [Finset.mul_sum]
    _ ≤ (1 + ∑ a, ∑ b, (2 * S a b ^ 2 * (P + Q) + 2 * S' a b ^ 2)) * t := by nlinarith

end PositivityTheory.RgHe3
