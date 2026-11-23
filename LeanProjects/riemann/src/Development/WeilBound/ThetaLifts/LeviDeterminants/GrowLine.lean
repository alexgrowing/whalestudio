import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowDef

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Line

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def lineFn (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ)) * f (p + t • A)

def lineD (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ)) *
    (-(2 * Real.pi * Complex.I) * ((L p + 2 * t * c : ℝ) : ℂ) * f (p + t • A) + fderiv ℝ f (p + t • A) A)

theorem hasDerivAt_lineFn (f : SchwartzMap V ℂ) (A : V) (L : V →L[ℝ] ℝ) (c : ℝ) (p : V) (t : ℝ) :
    HasDerivAt (lineFn f A L c p) (lineD f A L c p t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * L p + s ^ 2 * c) (L p + 2 * t * c) t := by
    have a1 : HasDerivAt (fun s : ℝ => s * L p) (L p) t := by simpa using (hasDerivAt_id t).mul_const (L p)
    have a2 : HasDerivAt (fun s : ℝ => s ^ 2 * c) (2 * t * c) t := by
      simpa using ((hasDerivAt_id t).pow 2).mul_const c
    exact a1.fun_add a2
  have h2 := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun s : ℝ => p + s • A) A t := by
    simpa using ((hasDerivAt_id t).smul_const A).const_add p
  have h4 : HasDerivAt (fun s : ℝ => f (p + s • A)) (fderiv ℝ f (p + t • A) A) t :=
    (f.hasFDerivAt (p + t • A)).comp_hasDerivAt t h3
  refine (h2.fun_mul h4).congr_deriv ?_
  simp only [lineD]
  push_cast
  ring

theorem lineD_bound (f : SchwartzMap V ℂ) (A A₀ : V) (L : V →L[ℝ] ℝ) (c : ℝ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : V) (t : ℝ), |t| ≤ 1 → ‖lineD f A L c (m + A₀) t‖ ≤ K * ((1 + ‖m‖) ^ k)⁻¹ := by
  set C₀ : ℝ := 2 ^ (k + 1) * (Finset.Iic (k + 1, 1)).sup (schwartzSeminormFamily ℂ V ℂ) f
  have hC0 : 0 ≤ C₀ := by positivity
  have b0 : ∀ q, (1 + ‖q‖) ^ (k + 1) * ‖f q‖ ≤ C₀ := fun q => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, 1)) (k := k + 1) (n := 0) le_rfl (by simp) f q
    rwa [norm_iteratedFDeriv_zero] at h
  have b1 : ∀ q, (1 + ‖q‖) ^ k * ‖fderiv ℝ f q‖ ≤ C₀ := fun q => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 1, 1)) (k := k + 1) (n := 1) le_rfl le_rfl f q
    rw [norm_iteratedFDeriv_one] at h
    refine le_trans ?_ h
    have hS : (1 : ℝ) ≤ 1 + ‖q‖ := by linarith [norm_nonneg q]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS (Nat.le_succ k)) (norm_nonneg _)
  set R : ℝ := ‖A₀‖ + ‖A‖ with hR
  have hR0 : 0 ≤ R := by positivity
  set B : ℝ := ‖L‖ * (1 + ‖A‖ + ‖A‖ ) + 2 * |c| with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(2 * Real.pi * B * C₀ + ‖A‖ * C₀) * (1 + R) ^ k, by positivity, fun m t ht => ?_⟩
  set p := m + A₀ with hp
  set q := p + t • A with hq
  have htA : ‖t • A‖ ≤ ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hpq : ‖p‖ ≤ ‖q‖ + ‖A‖ := by
    have : p = q - t • A := by simp [hq]
    rw [this]
    exact (norm_sub_le _ _).trans (by gcongr)
  have hmq : ‖m‖ ≤ ‖q‖ + R := by
    have : m = q - t • A - A₀ := by simp [hq, hp]
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le q (t • A)
    rw [hR]
    linarith
  set S : ℝ := 1 + ‖q‖ with hS
  have hS1 : 1 ≤ S := by rw [hS]; linarith [norm_nonneg q]
  have hS0 : 0 < S := by linarith
  have hSk : 0 < S ^ k := by positivity
  have hf : S * ‖f q‖ ≤ C₀ * (S ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hSk]
    have := b0 q
    calc S * ‖f q‖ * S ^ k = S ^ (k + 1) * ‖f q‖ := by ring
      _ ≤ C₀ := this
  have hdf : ‖fderiv ℝ f q‖ ≤ C₀ * (S ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hSk, mul_comm]
    exact b1 q
  have hLp : |L p + 2 * t * c| ≤ S * B := by
    have h1 : |L p| ≤ ‖L‖ * (‖q‖ + ‖A‖) :=
      (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left hpq (norm_nonneg _))
    have h2 : |2 * t * c| ≤ 2 * |c| := by
      rw [abs_mul, abs_mul, abs_two]
      have := abs_nonneg c
      nlinarith
    have h3 : ‖q‖ + ‖A‖ ≤ S * (1 + ‖A‖ + ‖A‖) := by
      have hA := norm_nonneg A
      have hq0 := norm_nonneg q
      nlinarith
    calc |L p + 2 * t * c| ≤ |L p| + |2 * t * c| := abs_add_le _ _
      _ ≤ ‖L‖ * (S * (1 + ‖A‖ + ‖A‖)) + S * (2 * |c|) := by
          have := mul_le_mul_of_nonneg_left h3 (norm_nonneg L)
          have h4 : 2 * |c| ≤ S * (2 * |c|) := le_mul_of_one_le_left (by positivity) hS1
          linarith
      _ = S * B := by rw [hB]; ring
  have hnorm : ‖lineD f A L c p t‖ ≤ (2 * Real.pi * B * C₀ + ‖A‖ * C₀) * (S ^ k)⁻¹ := by
    have hexp : ‖Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ))‖ = 1 := by
      have : -(2 * Real.pi * Complex.I) * ((t * L p + t ^ 2 * c : ℝ) : ℂ) =
          ((-(2 * Real.pi) * (t * L p + t ^ 2 * c) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hc : ‖-(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [lineD, norm_mul, hexp, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs]
    have h1 : 2 * Real.pi * |L p + 2 * t * c| * ‖f q‖ ≤ 2 * Real.pi * B * (C₀ * (S ^ k)⁻¹) := by
      calc 2 * Real.pi * |L p + 2 * t * c| * ‖f q‖ ≤ 2 * Real.pi * (S * B) * ‖f q‖ := by gcongr
        _ = 2 * Real.pi * B * (S * ‖f q‖) := by ring
        _ ≤ _ := by gcongr
    have h2 : ‖(fderiv ℝ f q) A‖ ≤ ‖A‖ * (C₀ * (S ^ k)⁻¹) := by
      refine ((fderiv ℝ f q).le_opNorm A).trans ?_
      rw [mul_comm]
      gcongr
    calc _ ≤ 2 * Real.pi * B * (C₀ * (S ^ k)⁻¹) + ‖A‖ * (C₀ * (S ^ k)⁻¹) := add_le_add h1 h2
      _ = _ := by ring
  refine hnorm.trans ?_
  have hT : 1 + ‖m‖ ≤ S * (1 + R) := by
    rw [hS]
    nlinarith [norm_nonneg q]
  have hT0 : 0 < 1 + ‖m‖ := by linarith [norm_nonneg m]
  have hinv : (S ^ k)⁻¹ ≤ (1 + R) ^ k * ((1 + ‖m‖) ^ k)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ hSk, ← mul_pow]
    exact pow_le_pow_left₀ hT0.le hT k
  calc _ ≤ (2 * Real.pi * B * C₀ + ‖A‖ * C₀) * ((1 + R) ^ k * ((1 + ‖m‖) ^ k)⁻¹) := by gcongr
    _ = _ := by ring

end Line

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  simp [evI, realAd]

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  simp [linForm, map_sum, LinearMap.sum_apply]

theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add, map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

omit [Fintype κ] in

theorem snd_eq_zero {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let w : AF F := LinearMap.inr F (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) 1
  have e0 : evI F w = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h : w * z i = 0 := congrFun (hz w e0) i
  have h2 : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (z i).2 = 0 := congrArg Prod.snd h
  simpa using h2

open scoped Classical in

theorem schr_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b : κ → AF F) (ha : At (evI F) a) (hb : At (evI F) b)
    (f : SInf F κ) (g : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ) (x : κ → AF F) (t : ℝ) :
    schr ψ (realAd F t • a, realAd F t • b) (pureA F f g) x =
      lineFn f (fun i => evI F (a i)) (linForm fun i => evI F (b i))
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)))
        (fun i => evI F (x i)) t * g (fun i => (x i).2) := by
  have hat : At (evI F) (realAd F t • a) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  have e : (fun i => evI F ((x + realAd F t • a) i)) = (fun i => evI F (x i)) + t • fun i => evI F (a i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  have e2 : (fun i => ((x + realAd F t • a) i).2) = fun i => (x i).2 := by
    funext i
    have h := snd_eq_zero hat i
    show (x i).2 + ((realAd F t • a) i).2 = (x i).2
    rw [h, add_zero]
  show ψ _ * (f (fun i => evI F ((x + realAd F t • a) i)) * g (fun i => ((x + realAd F t • a) i).2)) = _
  rw [phase_line ψ hψ a b x hb t, e, e2, lineFn]
  exact (mul_assoc _ _ _).symm

end PositivityTheory.ThKF0.Grow
