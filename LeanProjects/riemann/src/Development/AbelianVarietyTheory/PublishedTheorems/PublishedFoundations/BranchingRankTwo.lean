import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

open MvPolynomial Formalism.BasicNotions
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

noncomputable section

namespace GlobalTheory.Branching.RankTwo

theorem coeff_diag {σ : Type} [Fintype σ] (d : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => C (d v) * X v : σ → MvPolynomial σ ℂ) f) = (∏ v, d v ^ m v) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    have : aeval (fun v => C (d v) * X v : σ → MvPolynomial σ ℂ) (monomial s a) =
        monomial s ((∏ v, d v ^ s v) * a) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, algebraMap_eq]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]

theorem h12 : 1 + 1 = 2 := rfl

theorem coeff_res (lam : DomWeight 2) (g : GL (Fin 1) ℂ) (f : MvPolynomial (Fin 2 × Fin 2) ℂ) (m : Fin 2 × Fin 2 →₀ ℕ) :
    coeff m (sqAct ℂ 2 lam (embGL ℂ 1 2 h12 g) f) =
      (g 0 0) ^ (lam.w 1 + (m (0, 0) + m (0, 1) : ℕ)) * coeff m f := by
  have hg : g 0 0 ≠ 0 := by
    have := g.det_ne_zero
    simpa using this
  have e := embGL_apply ℂ h12 g
  have hM : (embGL ℂ 1 2 h12 g : Matrix (Fin 2) (Fin 2) ℂ) = !![g 0 0, 0; 0, 1] := by
    ext a b
    rw [e]
    fin_cases a <;> fin_cases b <;> simp
  have hr : Formalism.GradedWeylDivisibility.rowAct ℂ (n := 2) (embGL ℂ 1 2 h12 g : Matrix (Fin 2) (Fin 2) ℂ).transpose =
      aeval (fun v : Fin 2 × Fin 2 => C (if v.1 = 0 then g 0 0 else 1) * X v) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    rw [hM]
    fin_cases a <;> simp [Formalism.GradedWeylDivisibility.rowAct, Fin.sum_univ_two]
  have hd : detPow ℂ 2 (embGL ℂ 1 2 h12 g) lam.detShift = (g 0 0) ^ lam.w 1 := by
    simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hM, DomWeight.detShift]
    simp
  rw [sqAct, hr, hd, coeff_smul, coeff_diag, zpow_add₀ hg, zpow_natCast]
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, pow_add, mul_assoc]

theorem small_const (mu : DomWeight 1) (f : nablaSq ℂ 1 mu) :
    (f : MvPolynomial (Fin 1 × Fin 1) ℂ) = C (coeff 0 f.1) := by
  have h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW 1 1) f.1 mu.natW := f.2.1
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · by_contra hc
    have h1 := congrFun (h hc) 0
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simp [Formalism.GradedWeylDivisibility.colW, DomWeight.natW, DomWeight.detShift] at h1
    apply hm
    ext v
    rw [Subsingleton.elim v (0, 0)]
    simpa using h1.symm

theorem small_act (mu : DomWeight 1) (g : GL (Fin 1) ℂ) (f : nablaSq ℂ 1 mu) :
    sqRep ℂ 1 mu g f = (g 0 0) ^ mu.w 0 • f := by
  apply Subtype.ext
  rw [sqRep_coe, Submodule.coe_smul, small_const mu f]
  simp [sqAct, detPow, DomWeight.detShift, Formalism.GradedWeylDivisibility.rowAct]

theorem big_supp (lam : DomWeight 2) (f : nablaSq ℂ 2 lam) (m : Fin 2 × Fin 2 →₀ ℕ) (hm : coeff m f.1 ≠ 0) :
    ((m (0, 0) + m (1, 0) : ℕ) : ℤ) = lam.w 0 - lam.w 1 ∧ m (0, 1) = 0 ∧ m (1, 1) = 0 := by
  have h : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW 2 2) f.1 lam.natW := f.2.1
  have h0 := congrFun (h hm) 0
  have h1 := congrFun (h hm) 1
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h0 h1
  have ha : lam.w 1 ≤ lam.w 0 := lam.anti (by decide)
  simp [Formalism.GradedWeylDivisibility.colW, DomWeight.natW, DomWeight.detShift, Fintype.sum_prod_type, Fin.sum_univ_two] at h0 h1
  refine ⟨?_, h1⟩
  rw [h0]
  omega

theorem one_mem (mu : DomWeight 1) : (1 : MvPolynomial (Fin 1 × Fin 1) ℂ) ∈ nablaSq ℂ 1 mu := by
  have h0 : mu.natW = 0 := by
    funext i
    rw [Subsingleton.elim i 0]
    simp [DomWeight.natW, DomWeight.detShift]
  refine ⟨?_, ?_⟩
  · rw [h0]; exact isWeightedHomogeneous_one _ _
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro l j _
    simp

theorem mono_mem (lam : DomWeight 2) (a b : ℕ) (hab : ((a + b : ℕ) : ℤ) = lam.w 0 - lam.w 1) :
    (X (0, 0) ^ a * X (1, 0) ^ b : MvPolynomial (Fin 2 × Fin 2) ℂ) ∈ nablaSq ℂ 2 lam := by
  refine ⟨?_, ?_⟩
  · have : lam.natW = a • Formalism.GradedWeylDivisibility.colW 2 2 (0, 0) + b • Formalism.GradedWeylDivisibility.colW 2 2 (1, 0) := by
      funext i
      fin_cases i <;> simp [DomWeight.natW, DomWeight.detShift, Formalism.GradedWeylDivisibility.colW]
      omega
    rw [this]
    exact ((isWeightedHomogeneous_X ℂ _ _).pow a).mul ((isWeightedHomogeneous_X ℂ _ _).pow b)
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro l j hlj
    have hj : (0 : Fin 2) ≠ j := fun e => by subst e; exact absurd hlj (by simp)
    simp [Formalism.GradedWeylDivisibility.colAddGen, hj]

def Separates {H : Type} [Group H] (ι : H →* GL (Fin 1) ℂ) : Prop :=
  ∀ a b : ℤ, (∀ y, ι y 0 0 ^ a = ι y 0 0 ^ b) → a = b

variable {H : Type} [Group H] {ι : H →* GL (Fin 1) ℂ}

def one' (mu : DomWeight 1) : nablaSq ℂ 1 mu := ⟨1, one_mem mu⟩

theorem eq_smul_one (mu : DomWeight 1) (f : nablaSq ℂ 1 mu) : f = coeff 0 f.1 • one' mu := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  conv_lhs => rw [small_const mu f]
  simp [one', smul_eq_C_mul]

theorem supp_image (hs : Separates ι) (lam : DomWeight 2) (mu : DomWeight 1)
    (T : (smallRep ι mu).IntertwiningMap (resRep ι h12 lam)) (m : Fin 2 × Fin 2 →₀ ℕ)
    (hm : coeff m (T (one' mu)).1 ≠ 0) : mu.w 0 = lam.w 1 + (m (0, 0) : ℕ) := by
  apply hs
  intro y
  have e := T.isIntertwining _ _ y (one' mu)
  have e1 : smallRep ι mu y (one' mu) = (ι y 0 0) ^ mu.w 0 • one' mu := small_act mu (ι y) _
  rw [e1, map_smul] at e
  have e2 := congrArg (fun z : nablaSq ℂ 2 lam => coeff m z.1) e
  have e3 : coeff m (resRep ι h12 lam y (T (one' mu))).1 = _ := coeff_res lam (ι y) (T (one' mu)).1 m
  simp only [e3, Submodule.coe_smul, coeff_smul, smul_eq_mul] at e2
  have := mul_right_cancel₀ hm e2
  rw [this, (big_supp lam _ m hm).2.1, add_zero]

theorem eq_zero_of_one (lam : DomWeight 2) (mu : DomWeight 1)
    (T : (smallRep ι mu).IntertwiningMap (resRep ι h12 lam)) (h : T (one' mu) = 0) : T = 0 := by
  ext1
  ext1 f
  rw [eq_smul_one mu f, map_smul]
  simp [h]

theorem interlace_iff (lam : DomWeight 2) (mu : DomWeight 1) :
    Interlace h12 lam mu ↔ mu.w 0 ≤ lam.w 0 ∧ lam.w 1 ≤ mu.w 0 := by
  simp [Interlace]

theorem mult_zero (hs : Separates ι) (lam : DomWeight 2) (mu : DomWeight 1) (hn : ¬ Interlace h12 lam mu) :
    mult ι h12 lam mu = 0 := by
  rw [interlace_iff] at hn
  have : Subsingleton ((smallRep ι mu).IntertwiningMap (resRep ι h12 lam)) := by
    refine subsingleton_of_forall_eq 0 fun T => eq_zero_of_one lam mu T ?_
    apply Subtype.ext
    ext m
    by_contra hm
    have h1 := supp_image hs lam mu T m hm
    have h2 := (big_supp lam _ m hm).1
    push_cast at h2
    omega
  exact Module.finrank_zero_of_subsingleton

theorem mult_one (hs : Separates ι) (lam : DomWeight 2) (mu : DomWeight 1) (hn : Interlace h12 lam mu) :
    mult ι h12 lam mu = 1 := by
  rw [interlace_iff] at hn
  obtain ⟨a, ha⟩ : ∃ a : ℕ, mu.w 0 = lam.w 1 + a := ⟨(mu.w 0 - lam.w 1).toNat, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, lam.w 0 = mu.w 0 + b := ⟨(lam.w 0 - mu.w 0).toNat, by omega⟩
  let m0 : Fin 2 × Fin 2 →₀ ℕ := Finsupp.single (0, 0) a + Finsupp.single (1, 0) b
  have hmono : (X (0, 0) ^ a * X (1, 0) ^ b : MvPolynomial (Fin 2 × Fin 2) ℂ) = monomial m0 1 := by
    simp [m0, X_pow_eq_monomial, monomial_mul]
  let v : nablaSq ℂ 2 lam := ⟨_, mono_mem lam a b (by push_cast; omega)⟩
  have hv : ∀ m, coeff m v.1 = if m0 = m then 1 else 0 := fun m => by
    simp only [v, hmono, coeff_monomial]
  let L : nablaSq ℂ 1 mu →ₗ[ℂ] nablaSq ℂ 2 lam :=
    LinearMap.smulRight ((lcoeff ℂ 0).comp (nablaSq ℂ 1 mu).subtype) v
  have hL : ∀ f, L f = coeff 0 f.1 • v := fun _ => rfl
  have hvy : ∀ y, resRep ι h12 lam y v = (ι y 0 0) ^ mu.w 0 • v := fun y => by
    apply Subtype.ext
    ext m
    have e3 : coeff m (resRep ι h12 lam y v).1 = _ := coeff_res lam (ι y) v.1 m
    rw [e3, Submodule.coe_smul, coeff_smul, hv, smul_eq_mul]
    split_ifs with h
    · subst h
      simp [m0, ha]
    · simp
  let T0 : (smallRep ι mu).IntertwiningMap (resRep ι h12 lam) := L.intertwiningMap_of_isIntertwiningMap _ _
    fun y f => by
      have e1 : smallRep ι mu y f = (ι y 0 0) ^ mu.w 0 • f := small_act mu (ι y) _
      rw [e1, map_smul, hL, map_smul, hvy, smul_comm]
  have hT0 : T0 (one' mu) = v := by
    show L _ = v
    simp [hL, one']
  refine (finrank_eq_one_iff_of_nonzero' T0 ?_).2 fun T => ⟨coeff m0 (T (one' mu)).1, ?_⟩
  · intro h
    have h1 : v = 0 := by rw [← hT0, h]; rfl
    have := hv m0
    rw [h1] at this
    simp at this
  · have key : T (one' mu) = coeff m0 (T (one' mu)).1 • v := by
      apply Subtype.ext
      ext m
      rw [Submodule.coe_smul, coeff_smul, hv, smul_eq_mul]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
        by_contra hm
        have h1 := supp_image hs lam mu T m hm
        obtain ⟨h2, h3, h4⟩ := big_supp lam _ m hm
        push_cast at h2
        apply h
        ext ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> simp [m0] <;> omega
    ext1
    ext1 f
    show coeff m0 (T (one' mu)).1 • L f = T f
    conv_rhs => rw [eq_smul_one mu f, map_smul, key]
    rw [hL, smul_comm]

theorem separates_id : Separates (MonoidHom.id (GL (Fin 1) ℂ)) := by
  intro a b h
  have := h (Matrix.GeneralLinearGroup.mkOfDetNeZero !![2] (by simp))
  have h2 := congrArg norm this
  simp only [MonoidHom.id_apply, norm_zpow] at h2
  have e : ‖(Matrix.GeneralLinearGroup.mkOfDetNeZero (!![2] : Matrix (Fin 1) (Fin 1) ℂ) (by simp)) 0 0‖ = 2 := by
    show ‖(2 : ℂ)‖ = 2
    simp
  rw [e] at h2
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h2

theorem separates_unitary : Separates (unitaryIncl 1) := by
  intro a b h
  by_contra hab
  have hr : ((a - b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hab
  set t : ℝ := Real.pi / ((a - b : ℤ) : ℝ) with ht
  let z : ℂ := Complex.exp (t * Complex.I)
  have hz : z * star z = 1 := by
    have : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
    simp
  have hu : (!![z] : Matrix (Fin 1) (Fin 1) ℂ) ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i; fin_cases j
    simpa [Matrix.mul_apply] using hz
  have h1 : z ^ a = z ^ b := h ⟨_, hu⟩
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have h2 : z ^ (a - b) = 1 := by rw [zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]
  have h3 : z ^ (a - b) = -1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_pi_mul_I]
    congr 1
    have : ((a - b : ℤ) : ℝ) * t = Real.pi := by rw [ht]; field_simp
    rw [← this]
    push_cast
    ring
  rw [h2] at h3
  norm_num at h3

theorem mult_clause (lam : DomWeight 2) (mu : DomWeight 1) :
    ((Interlace h12 lam mu → mult (MonoidHom.id _) h12 lam mu = 1) ∧
      (¬ Interlace h12 lam mu → mult (MonoidHom.id _) h12 lam mu = 0)) ∧
    ((Interlace h12 lam mu → mult (unitaryIncl 1) h12 lam mu = 1) ∧
      (¬ Interlace h12 lam mu → mult (unitaryIncl 1) h12 lam mu = 0)) :=
  ⟨⟨mult_one separates_id lam mu, mult_zero separates_id lam mu⟩,
    ⟨mult_one separates_unitary lam mu, mult_zero separates_unitary lam mu⟩⟩

theorem standard_values :
    mult (unitaryIncl 1) h12 ⟨![1, 0], fun i j h => by fin_cases i <;> fin_cases j <;> simp_all⟩
        ⟨![1], fun i j _ => by rw [Subsingleton.elim i j]⟩ = 1 ∧
    mult (unitaryIncl 1) h12 ⟨![1, 0], fun i j h => by fin_cases i <;> fin_cases j <;> simp_all⟩
        ⟨![0], fun i j _ => by rw [Subsingleton.elim i j]⟩ = 1 ∧
    mult (unitaryIncl 1) h12 ⟨![1, 0], fun i j h => by fin_cases i <;> fin_cases j <;> simp_all⟩
        ⟨![-1], fun i j _ => by rw [Subsingleton.elim i j]⟩ = 0 :=
  ⟨mult_one separates_unitary _ _ (by simp [interlace_iff]), mult_one separates_unitary _ _ (by simp [interlace_iff]),
    mult_zero separates_unitary _ _ (by simp [interlace_iff])⟩

def expo (lam : DomWeight 2) (mu : DomWeight 1) : Fin 2 × Fin 2 →₀ ℕ :=
  Finsupp.single (0, 0) (mu.w 0 - lam.w 1).toNat + Finsupp.single (1, 0) (lam.w 0 - mu.w 0).toNat

theorem below_ext {lam : DomWeight 2} {mu nu : Below h12 lam} (h : mu.1.w 0 = nu.1.w 0) : mu = nu := by
  obtain ⟨⟨w, hw⟩, h1⟩ := mu
  obtain ⟨⟨w', hw'⟩, h2⟩ := nu
  have : w = w' := funext fun i => by rw [Subsingleton.elim i 0]; exact h
  subst this
  rfl

def comps (lam : DomWeight 2) [Fintype (Below h12 lam)] [DecidableEq (Below h12 lam)] :
    nablaSq ℂ 2 lam →ₗ[ℂ] (⨁ mu : Below h12 lam, nablaSq ℂ 1 mu.1) :=
  ∑ mu : Below h12 lam, (DirectSum.lof ℂ (Below h12 lam) (fun mu => nablaSq ℂ 1 mu.1) mu).comp
    (LinearMap.smulRight ((lcoeff ℂ (expo lam mu.1)).comp (nablaSq ℂ 2 lam).subtype) (one' mu.1))

theorem comps_apply (lam : DomWeight 2) [Fintype (Below h12 lam)] [DecidableEq (Below h12 lam)]
    (f : nablaSq ℂ 2 lam) (mu : Below h12 lam) : comps lam f mu = coeff (expo lam mu.1) f.1 • one' mu.1 := by
  simp only [comps, LinearMap.sum_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single mu]
  · rw [DirectSum.of_eq_same]; rfl
  · intro nu _ h
    exact DirectSum.of_eq_of_ne _ _ _ h.symm
  · simp

theorem one_ne (mu : DomWeight 1) : one' mu ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)

theorem comps_bijective (lam : DomWeight 2) [Fintype (Below h12 lam)] [DecidableEq (Below h12 lam)] :
    Function.Bijective (comps lam) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    ext m
    by_contra hm
    obtain ⟨h2, h3, h4⟩ := big_supp lam f m hm
    push_cast at h2
    let mu : Below h12 lam := ⟨⟨fun _ => lam.w 1 + m (0, 0), fun _ _ _ => le_rfl⟩, by
      rw [interlace_iff]; simp only; omega⟩
    have e : expo lam mu.1 = m := by
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [expo, mu] <;> omega
    have := comps_apply lam f mu
    rw [hf, e] at this
    exact hm ((smul_eq_zero.1 this.symm).resolve_right (one_ne _))
  · intro x
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨f + g, map_add _ _ _⟩
    | of mu x =>
      have hi := (interlace_iff _ _).1 mu.2
      have hmono : (X (0, 0) ^ (mu.1.w 0 - lam.w 1).toNat * X (1, 0) ^ (lam.w 0 - mu.1.w 0).toNat :
          MvPolynomial (Fin 2 × Fin 2) ℂ) = monomial (expo lam mu.1) 1 := by
        simp [expo, X_pow_eq_monomial, monomial_mul]
      let v : nablaSq ℂ 2 lam := ⟨_, mono_mem lam (mu.1.w 0 - lam.w 1).toNat (lam.w 0 - mu.1.w 0).toNat
        (by push_cast; omega)⟩
      refine ⟨coeff 0 x.1 • v, ?_⟩
      ext1 nu
      rw [comps_apply, Submodule.coe_smul, coeff_smul]
      simp only [v, hmono, coeff_monomial]
      by_cases h : nu = mu
      · subst h
        rw [DirectSum.of_eq_same, if_pos rfl, smul_eq_mul, mul_one, ← eq_smul_one]
      · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg, smul_zero, zero_smul]
        intro e
        apply h
        have hj := (interlace_iff _ _).1 nu.2
        have := congrArg (fun m : Fin 2 × Fin 2 →₀ ℕ => m (0, 0)) e
        simp [expo] at this
        exact below_ext (by omega)

theorem equiv_clause (ι : H →* GL (Fin 1) ℂ) (lam : DomWeight 2) :
    Nonempty ((sumRep ι h12 lam).Equiv (resRep ι h12 lam)) := by
  classical
  letI := Fintype.ofFinite (Below h12 lam)
  refine ⟨(Representation.Equiv.mk (ρ := resRep ι h12 lam) (σ := sumRep ι h12 lam)
    (LinearEquiv.ofBijective (comps lam) (comps_bijective lam)) fun y => ?_).symm⟩
  ext1 f
  ext1 mu
  have hi := (interlace_iff _ _).1 mu.2
  show comps lam (resRep ι h12 lam y f) mu = smallRep ι mu.1 y (comps lam f mu)
  have e1 : ∀ x, smallRep ι mu.1 y x = (ι y 0 0) ^ mu.1.w 0 • x := small_act mu.1 (ι y)
  have e3 : coeff (expo lam mu.1) (resRep ι h12 lam y f).1 = _ := coeff_res lam (ι y) f.1 _
  rw [e1, comps_apply, comps_apply, e3, mul_smul]
  congr 2
  simp [expo]
  omega

theorem branching_rank_two (lam : DomWeight 2) :
    BranchesAlong (MonoidHom.id (GL (Fin 1) ℂ)) h12 lam ∧ BranchesAlong (unitaryIncl 1) h12 lam :=
  ⟨⟨equiv_clause _ lam, fun mu => (mult_clause lam mu).1⟩, ⟨equiv_clause _ lam, fun mu => (mult_clause lam mu).2⟩⟩

end GlobalTheory.Branching.RankTwo
