import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticePointsIntegralIdelesEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZeroStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.ObjModel

namespace GlobalTheory.ToricSumValue

theorem cpow_pos_eq {r : ℝ} (hr : 0 < r) (z : ℂ) : (r : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le]

theorem term_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s) (σ : ℂ) (k : Eˣ) :
    term φ (2 * s) κ σ k = (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) *
      ((modF (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℝ) : ℂ) ^ ((s : ℂ) + σ) := by
  have hpos : ∀ i, 0 < ‖φ i (k : E)‖ := fun i => by simp
  have hN : 0 < ∏ i, ‖φ i (k : E)‖ ^ 2 := Finset.prod_pos fun i _ => pow_pos (hpos i) 2
  rw [modF_princ k, ← prod_normSq hφ k,
    Complex.cpow_add _ _ (by exact_mod_cast (inv_pos.2 hN).ne'), Complex.cpow_natCast]
  have h1 : term φ (2 * s) κ σ k = term φ (2 * s) κ 0 k * ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    unfold term
    rw [← Finset.prod_mul_distrib]
    simp
  have h2 : ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) = (((∏ i, ‖φ i (k : E)‖ ^ 2)⁻¹ : ℝ) : ℂ) ^ σ := by
    rw [cpow_pos_eq (inv_pos.2 hN), Real.log_inv, Real.log_prod (fun i _ => (pow_pos (hpos i) 2).ne')]
    simp only [cpow_pos_eq (hpos _)]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_pow]
    push_cast
    ring
  have h3 := term_mul_inf h k
  have h4 : ∏ i, (φ i k * starRingEnd ℂ (φ i k)) ^ s = (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s := by
    rw [Finset.prod_pow]
    congr 1
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.mul_conj' _
  have h5 : (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * (χ.inf k : ℂ) = 1 := by
    rw [← Units.val_mul, finPart_mul_inf, Units.val_one]
  rw [h4] at h3
  have hN' : (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [h1, h2, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_inv, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hN')]
  linear_combination (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * h3 -
    (term φ (2 * s) κ 0 k * (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s) * h5

def twistFin {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) : (Af E)ˣ →* ℂ where
  toFun y := (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S
  map_one' := by
    have : modF (1 : (Af E)ˣ) = 1 := modF_unit (c := ⊤) (one_mem _)
    simp [this]
  map_mul' y y' := by
    rw [map_mul, modF_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (modF_pos y).le (modF_pos y').le,
      Units.val_mul]
    ring

theorem twistFin_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) (y : (Af E)ˣ) :
    twistFin χ S y = (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S := rfl

theorem hasSum_classes {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s)
    {𝔣 c : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) (hd : 𝔣 ∣ c) (hc : c ≠ ⊥) (hχ : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    {σ T : ℂ} {S : PicO c → ℂ}
    (hS : ∀ q, HasSum (fun x : modUnits (lattice c q.out) => term φ (2 * s) κ σ x.1.out) (S q))
    (hT : HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ,
      (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} => twistFin χ (s + σ) z.1.out) T) :
    HasSum (fun q : PicO c => (twistFin χ (s + σ) q.out)⁻¹ * S q) T := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_latticePoints_integralIdeles_equiv E 𝔣 c h𝔣 hd hc
  rw [← e.hasSum_iff] at hT
  refine HasSum.sigma hT fun q => ?_
  refine ((hS q).mul_left (twistFin χ (s + σ) q.out)⁻¹).congr_fun fun x => ?_
  let k : Eˣ := Units.mk0 x.1.out (out_mem_lattice x).2
  have h1 := he ⟨q, x⟩ (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹) rfl
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (hatOUnits c)
    (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹)
  have h2 : twistFin χ (s + σ) u = 1 := by
    rw [twistFin_apply, hχ u u.2, modF_unit u.2]; simp
  have h3 : term φ (2 * s) κ σ x.1.out = twistFin χ (s + σ) (Units.map (algebraMap E (Af E)).toMonoidHom k) :=
    term_eq hφ h σ k
  show twistFin χ (s + σ) (e ⟨q, x⟩).1.out = _
  rw [h1, hu, map_mul, map_mul, h2, h3, mul_one, mul_comm, map_inv]

theorem toricSum_eq : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  intro hH E _ _ _ I _ φ hφ s κ 𝔣 Q χ Pq Λ hU hs h𝔣 hQ hχ hP hΛ
  classical
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hd : 𝔣 ∣ condQ 𝔣 Q := dvd_mul_right _ _
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hU h𝔣 hQ hχ
  have hfin := GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero E _ hc
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    GlobalTheory.T.exists_entire_latticeSum_of_heckeL_continuation hH E I φ hφ s κ 𝔣 _ χ hU hs h𝔣 hd hc hχ.1 hχ.2.2.1 htriv q.out
  refine ⟨hfin, S, hS, ?_⟩
  have := Fintype.ofFinite (PicO (condQ 𝔣 Q))
  have key : (fun σ : ℂ => ∑ q : PicO (condQ 𝔣 Q), (twistFin χ (s + σ) q.out)⁻¹ * S q σ) = fun σ : ℂ =>
      Λ (s + σ) * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)),
        ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) *
          (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) +
          ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) ^ 2) := by
    refine entire_eq_of_halfPlane ?_ ?_ (1 - s) fun σ hσ => ?_
    · refine Differentiable.fun_sum fun q _ => Differentiable.mul ?_ (hS q).1
      simp only [twistFin_apply, mul_inv, ← Complex.cpow_neg]
      refine Differentiable.const_mul ?_ _
      exact Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (modF_pos _).ne'))
    · refine (hΛ.1.comp (by fun_prop)).mul (Differentiable.fun_finsetProd fun q _ => ?_)
      have h0 : Differentiable ℂ fun σ : ℂ => (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ)) := by
        refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
        rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
        exact q.ne_bot
      fun_prop
    · have h1 : 1 < ((s : ℂ) + σ).re := by simp; linarith
      have h2 := GlobalTheory.T.hasSum_integralIdeles_eulerProduct E I φ hφ s κ 𝔣 Q χ Pq (s + σ) _ hU h𝔣 hQ hχ hP h1 (hΛ.2 _ h1)
      exact (hasSum_fintype _).unique (hasSum_classes hφ hχ.2.2.1 h𝔣 hd hc htriv
        (fun q => (hS q).2 σ (by push_cast; linarith)) h2)
  have h0 := congrFun key 0
  simp only [add_zero, twistFin_apply, Complex.cpow_neg, Complex.cpow_natCast] at h0
  rw [finsum_eq_sum_of_fintype]
  simp only [Formalism.PairingDivisionLocalBalance.eq, Complex.ofReal_pow]
  exact h0.symm

end GlobalTheory.ToricSumValue
