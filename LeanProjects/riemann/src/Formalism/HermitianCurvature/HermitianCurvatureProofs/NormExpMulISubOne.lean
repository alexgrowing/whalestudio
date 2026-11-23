import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice

noncomputable section

open Complex

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_exp_mul_I_sub_one (y : ℝ) : ‖Complex.exp ((y : ℂ) * I) - 1‖ ≤ |y| := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hs := Real.sin_sq_add_cos_sq y
  have e : (↑(Real.cos y) + ↑(Real.sin y) * I - 1 : ℂ) = ↑(Real.cos y - 1) + ↑(Real.sin y) * I := by
    push_cast; ring
  rw [e]
  have h2 : ‖(↑(Real.cos y - 1) + ↑(Real.sin y) * I : ℂ)‖ ^ 2 ≤ |y| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I, sq_abs]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 h2

theorem norm_exp_sub_one_of_re (z : ℂ) (hz : z.re = 0) : ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  have hz' : z = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hz]
  rw [hz']
  refine (norm_exp_mul_I_sub_one z.im).trans (le_of_eq ?_)
  rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem iter_add_const {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (i : ℕ) (f : E → F) (c : F) (x : E) :
    iteratedFDeriv ℝ (i + 1) (fun y => f y + c) x = iteratedFDeriv ℝ (i + 1) f x := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  congr 2
  funext y
  exact fderiv_add_const c

variable {k r : ℕ}

theorem mult_phase {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (D : Mat k r →L[ℝ] ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (A : ℝ) (F : Mat k r → E) (c : ℝ),
      CCle (A + ((m + 1 : ℕ) : ℝ)) m F c →
      CCle A m (fun g => (Complex.exp (PBFV.phaseL σ D g) - 1) • F g) (K * ‖σ‖ * c) := by
  obtain ⟨C1, hC1, hdlr⟩ := Formalism.FourierDecayAlt.P.JCx4.dlr_bound (k := k) (r := r) (E := E →L[ℂ] E) m
  obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ M : Mat k r, ‖D M‖ ≤ K * ‖M‖ := ⟨_, D.le_opNorm⟩
  set KD : ℝ := max K0 0 with hKDdef
  have hKD0 : 0 ≤ KD := le_max_right _ _
  have hKD : ∀ M : Mat k r, ‖D M‖ ≤ KD * ‖M‖ := fun M =>
    (hK0 M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set Lid : ℂ →L[ℝ] (E →L[ℂ] E) :=
    ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℂ E) with hLid
  set L : ℝ := 1 + 4 * KD with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  set K : ℝ := 2 ^ m * (C1 * (2 ^ m * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (2 * KD * (1 + L ^ m)))))) with hKdef
  refine ⟨K, by positivity, ?_⟩
  intro σ hσ A F c hF
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hF
  set θ : Mat k r →L[ℝ] ℂ := PBFV.phaseL σ D with hθdef
  have hθ0 : ∀ g, (θ g).re = 0 := PBFV.phaseL_re σ D
  set t : ℝ := 2 * ‖σ‖ * KD with htdef
  have ht0 : 0 ≤ t := by positivity
  have htL : t ≤ L := by
    rw [htdef, hLdef]
    have : ‖σ‖ * KD ≤ 2 * KD := mul_le_mul_of_nonneg_right hσ hKD0
    linarith
  have hθM : ∀ M : Mat k r, ‖θ M‖ ≤ t * ‖M‖ := by
    intro M
    rw [hθdef, PBFV.phaseL_apply]
    calc ‖σ * D M - (starRingEnd ℂ) (σ * D M)‖ ≤ ‖σ * D M‖ + ‖(starRingEnd ℂ) (σ * D M)‖ := norm_sub_le _ _
      _ = 2 * (‖σ‖ * ‖D M‖) := by rw [Complex.norm_conj, norm_mul]; ring
      _ ≤ 2 * (‖σ‖ * (KD * ‖M‖)) := by gcongr; exact hKD M
      _ = t * ‖M‖ := by rw [htdef]; ring
  have hθK := θ.opNorm_le_bound ht0 hθM
  have hexp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  set f0 : Mat k r → ℂ := fun g => Complex.exp (θ g) with hf0def
  have hf0 : ContDiff ℝ ⊤ f0 := hexp.comp θ.contDiff
  have hit0 : ∀ i g, ‖iteratedFDeriv ℝ i f0 g‖ ≤ t ^ i := by
    intro i g
    have h2 : iteratedFDeriv ℝ i f0 g =
        (iteratedFDeriv ℝ i Complex.exp (θ g)).compContinuousLinearMap (fun _ => θ) :=
      θ.iteratedFDeriv_comp_right (f := Complex.exp) hexp g (by exact_mod_cast le_top)
    have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i Complex.exp (θ g)) (fun _ : Fin i => θ)
    have h5 := h3.trans (mul_le_mul (le_of_eq (by rw [PBFV.norm_iter_cexp, hθ0, Real.exp_zero]))
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hθK))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
    rw [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
    rw [h2]; exact h5
  set f1 : Mat k r → ℂ := fun g => f0 g + (-1 : ℂ) with hf1def
  have hf1 : ContDiff ℝ ⊤ f1 := hf0.add contDiff_const
  set Λ : Mat k r → (E →L[ℂ] E) := fun g => Lid (f1 g) with hΛdef
  have hΛ : ∀ g, Λ g = (Complex.exp (θ g) - 1) • ContinuousLinearMap.id ℂ E := fun g => by
    simp [Λ, Lid, f1, f0, sub_eq_add_neg]
  have hΛc : ContDiff ℝ ⊤ Λ := Lid.contDiff.comp hf1
  have hitΛ : ∀ i, i ≤ m → ∀ g, ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * (t * (‖g‖ + L ^ m)) := by
    intro i hi g
    have h1 := Lid.norm_iteratedFDeriv_comp_left (f := f1) (x := g) (N := ⊤) (n := i)
      hf1.contDiffAt (by exact_mod_cast le_top)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rcases i with _ | j
    · rw [norm_iteratedFDeriv_zero]
      have e1 : f1 g = Complex.exp (θ g) - 1 := by simp [f1, f0, sub_eq_add_neg]
      rw [e1]
      calc ‖Complex.exp (θ g) - 1‖ ≤ ‖θ g‖ := norm_exp_sub_one_of_re _ (hθ0 g)
        _ ≤ t * ‖g‖ := hθM g
        _ ≤ t * (‖g‖ + L ^ m) := by
          have : 0 ≤ L ^ m := by positivity
          nlinarith
    · rw [show f1 = fun y => f0 y + (-1 : ℂ) from rfl, iter_add_const]
      calc ‖iteratedFDeriv ℝ (j + 1) f0 g‖ ≤ t ^ (j + 1) := hit0 _ g
        _ = t * t ^ j := by ring
        _ ≤ t * L ^ m := by
          refine mul_le_mul_of_nonneg_left ?_ ht0
          calc t ^ j ≤ L ^ j := pow_le_pow_left₀ ht0 htL j
            _ ≤ L ^ m := pow_le_pow_right₀ hL1 (by omega)
        _ ≤ t * (‖g‖ + L ^ m) := by
          have : 0 ≤ ‖g‖ := norm_nonneg _
          nlinarith
  set Cm : ℝ := C1 * (2 ^ m * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (1 + L ^ m))))) with hCm
  have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
        ‖dLR u v Λ g‖ ≤ Cm * gN g ^ (((m + 1 : ℕ) : ℕ) : ℝ) := by
    intro u v hu hv hl g hg _
    rw [Real.rpow_natCast]
    have h1 := hdlr Λ (hΛc.of_le (by exact_mod_cast le_top)) u v hu hv hl g
    have hg1 : 1 ≤ gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have hng : ‖g‖ ≤ gN g := Formalism.FourierDecayAlt.P.JCx2.mn_norm_le_gN g
    have hsum : ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ ≤
        ((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (‖g‖ + L ^ m))) := by
      calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖
          ≤ ∑ _i ∈ Finset.range (m + 1), ‖Lid‖ * (t * (‖g‖ + L ^ m)) :=
            Finset.sum_le_sum fun i hi => hitΛ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) g
        _ = ((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * (‖g‖ + L ^ m))) := by simp
    have hpow : (1 + ‖g‖) ^ m ≤ 2 ^ m * gN g ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hgL : ‖g‖ + L ^ m ≤ (1 + L ^ m) * gN g := by
      have : 0 ≤ L ^ m := by positivity
      nlinarith
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hLid0 : 0 ≤ ‖Lid‖ := norm_nonneg _
    calc ‖dLR u v Λ g‖ ≤ C1 * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ := h1
      _ ≤ C1 * (2 ^ m * gN g ^ m) * (((m + 1 : ℕ) : ℝ) * (‖Lid‖ * (t * ((1 + L ^ m) * gN g)))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC1) (hsum.trans ?_) hS0
          · exact mul_nonneg hC1 (by positivity)
          · gcongr
      _ = Cm * gN g ^ (m + 1) := by rw [hCm]; ring
  have ha : CkOn (m : ℕ∞) Set.univ Λ := fun g₀ _ =>
    ⟨Set.univ, Λ, isOpen_univ, trivial, (hΛc.of_le (by exact_mod_cast le_top)).contDiffOn, fun _ _ _ => rfl⟩
  have hb' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
    (A := A) (d := (((m + 1 : ℕ) : ℕ) : ℝ)) ha hab hF (fun g _ h => h.elim)
  have e : (fun g => (Complex.exp (PBFV.phaseL σ D g) - 1) • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap Λ F := by
    funext g
    simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ, θ]
  rw [e]
  refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (le_of_eq ?_)
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  rw [abs_of_nonneg hCm0, abs_of_nonneg hc0, hCm, hKdef, htdef]
  ring

end Formalism.FourierDecayAlt.P.StandardPairingDecay
