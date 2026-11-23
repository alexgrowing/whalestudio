import Formalism.EllipticTorsion.Statement

noncomputable section

open PowerSeries

namespace Formalism.ELL.SubstitutionCoefficientCongruence

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_subst_congr_lemma {R : Type*} [CommRing R] {σ : Type*}
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (n : ℕ) :
    ∀ e : σ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (a ^ n) = 0 := by
  classical
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    intro e he
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : x.2 = 0
    · have h0 : MvPowerSeries.coeff 0 a = 0 := by
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha]
      rw [h2, h0, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
      have hsum : x.1.degree + x.2.degree = e.degree := by rw [← map_add, hx]
      have h1 : x.1.degree < n := by omega
      rw [ih x.1 h1, zero_mul]

theorem coeff_subst_congr {g h : PowerSeries R} {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (e : σ →₀ ℕ)
    (hgh : ∀ k ≤ e.degree, coeff k g = coeff k h) :
    MvPowerSeries.coeff e (g.subst a) = MvPowerSeries.coeff e (h.subst a) := by
  classical
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k ≤ e.degree
  · rw [hgh k hk]
  · rw [coeff_subst_congr_lemma ha k e (by omega), smul_zero, smul_zero]

theorem pderiv_subst_coe (p : Polynomial R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv R i ((p : PowerSeries R).subst a) =
      (derivative R (p : PowerSeries R)).subst a * MvPowerSeries.pderiv R i a := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  suffices H : ∀ P : Polynomial R, MvPowerSeries.pderiv R i (PowerSeries.substAlgHom hs (P : PowerSeries R)) =
      PowerSeries.substAlgHom hs (derivative R (P : PowerSeries R)) * MvPowerSeries.pderiv R i a by
    simpa only [PowerSeries.coe_substAlgHom] using H p
  intro P
  induction P using Polynomial.induction_on'
  next P Q hP hQ =>
    rw [Polynomial.coe_add, map_add, map_add, hP, hQ, map_add, map_add, add_mul]
  next n c =>
    have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries R) = a := by
      rw [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
    rw [← Polynomial.smul_X_eq_monomial]
    simp only [Polynomial.coe_smul, Polynomial.coe_pow, Polynomial.coe_X, map_smul, map_pow, hX,
      Derivation.map_smul, Derivation.leibniz_pow, PowerSeries.derivative_X, map_nsmul, smul_eq_mul,
      mul_one, map_mul, map_one, nsmul_eq_mul, map_natCast, smul_mul_assoc, mul_assoc]

theorem degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, map_add]
  exact Nat.le_add_right _ _

theorem pderiv_subst (g : PowerSeries R) {a : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (i : σ) :
    MvPowerSeries.pderiv R i (g.subst a) =
      (derivative R g).subst a * MvPowerSeries.pderiv R i a := by
  classical
  ext e
  have hP : ∀ k ≤ e.degree + 1,
      coeff k ((PowerSeries.trunc (e.degree + 2) g : Polynomial R) : PowerSeries R) = coeff k g := by
    intro k hk
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega)]
  have hdeg : (e + Finsupp.single i 1).degree = e.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv R i (g.subst a)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv R i
        (((PowerSeries.trunc (e.degree + 2) g : Polynomial R) : PowerSeries R).subst a)) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
      coeff_subst_congr ha _ (fun k hk => (hP k (by omega)).symm)]
  rw [h1, pderiv_subst_coe _ ha i, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxd := degree_le_of_mem_antidiagonal hx
  rw [coeff_subst_congr ha x.1 (fun k hk => ?_)]
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, hP (k + 1) (by omega)]

end Chain

section Integral

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

theorem mem_unitBall {x : K} : x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem integral_one : Formalism.G.IntegralMv (1 : MvPowerSeries σ K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem integral_mul {F G : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F)
    (hG : Formalism.G.IntegralMv G) : Formalism.G.IntegralMv (F * G) := by
  classical
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ =>
    Subring.mul_mem _ (mem_unitBall.2 (hF _)) (mem_unitBall.2 (hG _))

theorem integral_pow {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (n : ℕ) :
    Formalism.G.IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hF

theorem integral_pderiv {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (i : σ) :
    Formalism.G.IntegralMv (MvPowerSeries.pderiv K i F) := by
  intro d
  rw [← mem_unitBall, MvPowerSeries.coeff_pderiv]
  refine Subring.mul_mem _ (mem_unitBall.2 (hF _)) ?_
  exact Subring.add_mem _ (natCast_mem _ _) (Subring.one_mem _)

theorem integral_subst {c : PowerSeries K} (hc : ∀ n, ‖coeff n c‖ ≤ 1)
    {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : Formalism.G.IntegralMv f) : Formalism.G.IntegralMv (c.subst f) := by
  classical
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf0
  intro e
  rw [← mem_unitBall, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (e.degree + 1)) ?_]
  · exact Subring.sum_mem _ fun d _ => by
      rw [smul_eq_mul]
      exact Subring.mul_mem _ (mem_unitBall.2 (hc d)) (mem_unitBall.2 (integral_pow hf d e))
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [coeff_subst_congr_lemma hf0 d e (by omega), smul_zero])

end Integral

end Formalism.ELL.SubstitutionCoefficientCongruence

namespace Formalism.ELL

theorem N_partial_derivative : NPderiv := by
  intro K _ _ _ σ G hG i
  obtain ⟨f, hf0, hf, rfl⟩ := hG
  unfold logOnePlus
  rw [SubstitutionCoefficientCongruence.pderiv_subst _ hf0]
  refine SubstitutionCoefficientCongruence.integral_mul ?_ (SubstitutionCoefficientCongruence.integral_pderiv hf i)
  refine SubstitutionCoefficientCongruence.integral_subst ?_ hf0 hf
  intro n
  unfold PowerSeries.log
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n)]
  have hn : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [map_div₀, map_pow, map_neg, map_one, map_natCast, Nat.cast_succ, div_mul_cancel₀ _ hn,
    norm_pow, norm_neg, norm_one, one_pow]

end Formalism.ELL
