import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinNumN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobeniusTraceCountBoundOfCmEigensystemCount

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br
namespace UpperTheory.GalN.V.Win.N
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.CongNum
section
private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top
private theorem est {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) {t z₁ z₂ z₃ : ℂ} (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (ht : ‖t‖ ≤ 3 * (Real.sqrt p * (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) + (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) :
    t - eis4 p e z₁ z₂ z₃ ≠ 0 ∧ ‖t - eis4 p e z₁ z₂ z₃‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2) with hx
  set y : ℝ := (p : ℝ) ^ e with hy
  have hx0 : 0 ≤ x := by positivity
  have hxx : x * x = p * y := by
    rw [hx, ← Real.rpow_add (by linarith), hy, ← pow_succ', ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hy2 : (p : ℝ) ^ 2 ≤ y := pow_le_pow_right₀ (by linarith) he
  have hy0 : 0 ≤ y := by positivity
  have hxy : 2 * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0, mul_nonneg (show (0:ℝ) ≤ p - 4 by linarith) (mul_nonneg (show (0:ℝ) ≤ p by linarith) hy0)]
  have hsx : Real.sqrt p * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    rw [mul_pow, Real.sq_sqrt (by linarith), pow_two x, hxx]
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  replace ht : ‖t‖ ≤ 7 / 2 * y := by linarith
  have n1 : ‖(p : ℂ) ^ (e + 1) * z₁‖ = p * y := by simp [h1, hy, pow_succ']
  have n2 : ‖(p : ℂ) ^ e * z₂‖ = y := by simp [h2, hy]
  have n3 : ‖(p : ℂ) * z₃‖ = p := by simp [h3]
  have hr : ‖t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)‖ ≤ 7 / 2 * y + (y + p + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ht ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, ← n2, ← n3]
    have := norm_add_le ((p : ℂ) ^ e * z₂) ((p : ℂ) * z₃)
    simpa using this
  have hE : t - eis4 p e z₁ z₂ z₃ = (t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)) - (p : ℂ) ^ (e + 1) * z₁ := by
    rw [eis4]; ring
  have hlt : 7 / 2 * y + (y + p + 1) < p * y := by nlinarith
  constructor
  · intro h0
    rw [hE, sub_eq_zero] at h0
    rw [h0, n1] at hr
    linarith
  · rw [hE]
    refine (norm_sub_le _ _).trans ?_
    rw [n1, mul_comm 2, pow_mul, pow_succ' (p : ℝ) e, ← hy]
    have : (2 : ℝ) ≤ p * y := by nlinarith
    nlinarith
private theorem size {c A M e N d p : ℕ} (hN : N ≤ c * (M * (e + 1 + 1)) ^ A) (hM : 1 ≤ M) (hp : 5 ≤ p) :
    ((N * d : ℕ) : ℝ) * Real.log ((p : ℝ) ^ (2 * (e + 1))) ≤
      ((c * 2 ^ A * 2 : ℕ) : ℝ) * d * ((M : ℝ) * (e + 1)) ^ (A + 1) * Real.log p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : N * d * (2 * (e + 1)) ≤ c * 2 ^ A * 2 * d * (M * (e + 1)) ^ (A + 1) := by
    have a1 : (M * (e + 1 + 1)) ^ A ≤ 2 ^ A * (M * (e + 1)) ^ A := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) _
    have a2 : e + 1 ≤ M * (e + 1) := Nat.le_mul_of_pos_left _ hM
    calc N * d * (2 * (e + 1)) ≤ c * (2 ^ A * (M * (e + 1)) ^ A) * d * (2 * (M * (e + 1))) := by
          gcongr
          exact hN.trans (by gcongr)
      _ = _ := by ring
  rw [Real.log_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact_mod_cast h1
end
open UpperTheory.V.Af in
theorem number_sp4_of_admissible_to_admissible_n :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelPNAlt → _root_.UpperTheory.GalN.V.AdmResNAlt →
    (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin 4 → ℤ) (wt : ℤ)
      (r : G ℚ Ω →* GL (Fin 4) (Qbar l)), _root_.UpperTheory.V.Af.AdmRAlt ι M m wt r → _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r) →
    _root_.UpperTheory.V.Af.NumberSp4Alt := by
  intro hP hLP hA hR
  obtain ⟨c, A, hc⟩ := _root_.UpperTheory.GalN.V.Win.N.countQ_alt hP hLP hA 4 (by norm_num)
  refine ⟨c * 2 ^ A * 2, A + 1, fun e he M hM p w hp hw h5 hpM k hk z₁ z₂ z₃ h1 h2 h3 => ?_⟩
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨D, hD, hcl⟩ := hc ![(e : ℤ) + 1, e, 1, 0] (e + 1)
    (by
      rw [Fin.strictAnti_iff_succ_lt]
      intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp [Fin.rev] <;> omega) (e + 1)
    (by intro i; fin_cases i <;> simp [abs_le] <;> omega) M hM p w hp hw hpM
  haveI := D.fin
  letI := Fintype.ofFinite D.S
  let f : D.S × (ZMod k)ˣ → ℂ := fun x =>
    (D.β x.1).sum - eis4 p e (z₁ ^ (x.2 : ZMod k).val) (z₂ ^ (x.2 : ZMod k).val) (z₃ ^ (x.2 : ZMod k).val)
  have hzi : ∀ z : ℂ, z ^ k = 1 → IsIntegral ℤ z := fun z hz => IsIntegral.of_pow hk (hz ▸ isIntegral_one)
  have hzn : ∀ z : ℂ, z ^ k = 1 → ∀ a : ℕ, ‖z ^ a‖ = 1 := fun z hz a => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hk.ne', one_pow]
  have hi : ∀ x, IsIntegral ℤ (f x) := fun x => by
    have hpi : IsIntegral ℤ (p : ℂ) := isIntegral_natCast p
    refine IsIntegral.sub (IsIntegral.multiset_sum fun b hb => ?_) ?_
    · simpa using D.int 0 (by intro i; fin_cases i <;> simp <;> omega) x.1 b hb
    · exact ((((hpi.pow _).mul ((hzi _ h1).pow _)).add ((hpi.pow _).mul ((hzi _ h2).pow _))).add
        (hpi.mul ((hzi _ h3).pow _))).add isIntegral_one
  have hconj : ∀ σ : ℂ ≃+* ℂ, ∃ u : D.S × (ZMod k)ˣ ≃ D.S × (ZMod k)ˣ, ∀ x, f (u x) = σ (f x) := fun σ => by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨b, hb⟩ := exists_unit_pow k σ
    refine ⟨u.prodCongr (Equiv.mulLeft b), fun x => ?_⟩
    simp only [f, eis4, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hu, Equiv.coe_mulLeft, Units.val_mul, map_sub,
      map_add, map_mul, map_pow, map_one, map_natCast, map_multiset_sum, hb _ h1, hb _ h2, hb _ h3,
      pow_val_mul h1, pow_val_mul h2, pow_val_mul h3]
  have hest : ∀ x, f x ≠ 0 ∧ ‖f x‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := fun x => by
    refine est h5 he (hzn _ h1 _) (hzn _ h2 _) (hzn _ h3 _) ?_
    simpa only [Nat.cast_ofNat] using WinC.sum_le (D.pure x.1) (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) (n := 3) (D.card _)
  obtain ⟨NN, hNN⟩ := exists_int_prod f hi hconj
  obtain ⟨h0, hlog⟩ := log_abs_le f NN hNN (fun x => (hest x).1) _ fun x => (hest x).2
  refine ⟨NN, h0, hlog.trans ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ X hX hX' => ?_⟩
  · rw [Fintype.card_prod, ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact size hD hM h5
  replace hX := fun r hr => hR Ω l ι _ _ _ r (hX r hr)
  obtain ⟨cl, hinj, hfr⟩ := hcl l hl2 hlp Ω ι
  have hone : ∀ z : ℂ, z ^ k = 1 → z ^ (((1 : (ZMod k)ˣ) : ZMod k)).val = z := fun z hz => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  have key : ∀ (r) (hr : r ∈ X), (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃) =
      ι.symm (f (cl ⟨r, hX r hr⟩, 1)) := fun r hr => by
    have h := (hfr ⟨r, hX r hr⟩ B hB).2 σ (by rwa [normV_rat hp w hw])
    rw [map_inv] at h
    rw [trace_eq_sum_of_inv ι _ _ h]
    simp only [f, hone _ h1, hone _ h2, hone _ h3, map_sub]
  refine ⟨fun r hr h => ?_, ?_⟩
  · have := key r hr
    rw [h, sub_self, eq_comm, map_eq_zero_iff _ ι.symm.injective] at this
    exact (hest _).1 this
  · have := norm_le_prod ι f hi NN hNN (fun r : X => (cl ⟨r.1, hX r.1 r.2⟩, (1 : (ZMod k)ˣ))) fun r r' h =>
      Subtype.ext (hX' _ r.2 _ r'.2 (hinj _ _ (congrArg Prod.fst h)))
    refine this.trans_eq ?_
    rw [← Finset.prod_coe_sort X]
    exact Finset.prod_congr rfl fun r _ => by rw [key r.1 r.2]
end
end UpperTheory.GalN.V.Win.N
end
