import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt

namespace ReciprocityTheory.AnForm.A

open Matrix Filter Topology
open scoped ComplexOrder

noncomputable section

section Helpers

variable {D : ℕ}

theorem fderiv_cplx (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    fderiv ℝ (cplx v) z = Complex.ofRealCLM.comp (fderiv ℝ v z) := by
  by_cases h : DifferentiableAt ℝ v z
  · exact (Complex.ofRealCLM.hasFDerivAt.comp z h.hasFDerivAt).fderiv
  · have h' : ¬ DifferentiableAt ℝ (cplx v) z := by
      intro hc
      apply h
      have : v = fun y => Complex.reCLM (cplx v y) := by funext y; simp [cplx]
      rw [this]
      exact Complex.reCLM.differentiableAt.comp z hc
    rw [fderiv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h']
    simp

theorem dz_cplx (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dz j (cplx v) z = ((fderiv ℝ v z (Pi.single j 1) : ℂ) -
      Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ)) / 2 := by
  simp only [dz, fderiv_cplx, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

theorem dzb_cplx (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dzb j (cplx v) z = ((fderiv ℝ v z (Pi.single j 1) : ℂ) +
      Complex.I * (fderiv ℝ v z (Complex.I • Pi.single j 1) : ℂ)) / 2 := by
  simp only [dzb, fderiv_cplx, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

theorem dzb_cplx_eq_star (j : Fin D) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    dzb j (cplx v) z = star (dz j (cplx v) z) := by
  rw [dz_cplx, dzb_cplx]
  apply Complex.ext <;> simp

theorem gradMat_eq_vecMulVec (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    gradMat v w z = vecMulVec (fun j => dz j (cplx v) z) (star fun k => dz k (cplx w) z) := by
  ext j k
  simp [gradMat, vecMulVec_apply, dzb_cplx_eq_star]

theorem gradMat_swap (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    gradMat w v z = (gradMat v w z)ᴴ := by
  rw [gradMat_eq_vecMulVec, gradMat_eq_vecMulVec, conjTranspose_vecMulVec, star_star]

end Helpers

section Levi

variable {e : ℕ}

theorem leviC_add_snd (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a b b' : Fin e → ℂ) :
    leviC H a (b + b') = leviC H a b + leviC H a b' := by
  simp only [leviC, smul_add, map_add]
  push_cast
  ring

theorem leviC_smul_snd (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin e → ℂ) :
    leviC H a (c • b) = star c * leviC H a b := by
  have h1 : c • b = c.re • b + c.im • (Complex.I • b) := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have h2 : Complex.I • (c • b) = c.re • (Complex.I • b) - c.im • b := by
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * b k) * Complex.I_sq
  unfold leviC
  rw [h2, h1]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem sum_leviC_mul (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a x : Fin e → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by
  have hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin e → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single (star x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let ℓ : (Fin e → ℂ) →+ ℂ := AddMonoidHom.mk' (fun b => leviC H a b) (leviC_add_snd H a)
  rw [hx]
  show _ = ℓ _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ℓ, AddMonoidHom.mk'_apply, leviC_smul_snd, star_star]
  ring

theorem hessC_isHermitian_of_symm (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (h : IsSymmSndFDerivAt ℝ φ z) : (hessC φ z).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, hessC_eq_leviC, leviC]
  rw [h (Pi.single j 1) (Pi.single i 1), h (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1),
    h (Pi.single j 1) (Complex.I • Pi.single i 1), h (Complex.I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem hessC_posSemidef_of_levi (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (h2 : ContDiffAt ℝ 2 φ z)
    (hl : ∀ ξ, 0 ≤ levi φ z ξ) : (hessC φ z).PosSemidef := by
  have hs : IsSymmSndFDerivAt ℝ φ z := h2.isSymmSndFDerivAt (by simp)
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian_of_symm φ z hs) fun x => ?_
  have key : star x ⬝ᵥ (hessC φ z *ᵥ x) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x) := by
    simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
    exact sum_mul_leviC _ (star x) (star x)
  rw [key, Complex.nonneg_iff]
  constructor
  · have := hl (star x)
    simpa [leviC, levi] using this
  · simp only [leviC]
    rw [hs (star x) (Complex.I • star x)]
    simp

end Levi

section MatrixLemmas

variable {n : ℕ}

theorem re_mdisc_cons_conjTranspose (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).IsHermitian) :
    (mdisc (Fin.cons Aᴴ B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re =
      (mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
  have h : (Fin.cons Aᴴ B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun k => ((Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k)ᴴ := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp
    · simp [(hB i).eq]
  rw [h, ← star_mdisc]
  simp

theorem mdisc_cons_smul_add (c c' : ℂ) (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • A + c' • A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        c' * mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [mdisc_cons_eq_sum, mdisc_cons_eq_sum, mdisc_cons_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem mdisc_cons_smul_fst (c : ℂ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • A) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have := mdisc_cons_smul_add c 0 A A B
  simpa using this

theorem re_mdisc_cons_vecMulVec_nonneg (a : Fin (n + 1) → ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).PosSemidef) :
    0 ≤ (mdisc (Fin.cons (vecMulVec a (star a)) B :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
  refine (mdisc_nonneg_of_posSemidef _ fun k => ?_).2
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using posSemidef_vecMulVec_self_star a
  · simpa using hB i

theorem re_mdisc_cons_cs (a b : Fin (n + 1) → ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).PosSemidef) :
    (mdisc (Fin.cons (vecMulVec a (star b)) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re ^ 2 ≤
      (mdisc (Fin.cons (vecMulVec a (star a)) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re *
      (mdisc (Fin.cons (vecMulVec b (star b)) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by
  set S : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ) → ℂ := fun x y =>
    mdisc (Fin.cons (vecMulVec x (star y)) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    with hS
  have hsym : (S b a).re = (S a b).re := by
    simp only [hS]
    rw [← re_mdisc_cons_conjTranspose _ B (fun i => (hB i).1), conjTranspose_vecMulVec, star_star]
  have hq : ∀ t : ℝ, 0 ≤ (S b b).re * (t * t) + (2 * (S a b).re) * t + (S a a).re := by
    intro t
    have h := re_mdisc_cons_vecMulVec_nonneg (a + (t : ℂ) • b) B hB
    have key : mdisc (Fin.cons (vecMulVec (a + (t : ℂ) • b) (star (a + (t : ℂ) • b))) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        S a a + (t : ℂ) * (S a b + S b a) + ((t * t : ℝ) : ℂ) * S b b := by
      simp only [hS, mdisc_cons_eq_sum, vecMulVec_apply, Finset.mul_sum, mul_add,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_add, star_mul',
        Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [key] at h
    simp only [Complex.add_re, Complex.re_ofReal_mul] at h
    rw [hsym] at h
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  simp only [hS] at hd
  nlinarith [hd]

end MatrixLemmas

section Statements

variable {n : ℕ}

theorem dz_cplx_mul {D : ℕ} (j : Fin D) (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (cplx fun y => f y * g y) z = (f z : ℂ) * dz j (cplx g) z + (g z : ℂ) * dz j (cplx f) z := by
  rw [dz_cplx, dz_cplx, dz_cplx, HasFDerivAt.fderiv (f := fun y => f y * g y) (hf.hasFDerivAt.mul hg.hasFDerivAt)]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  ring

theorem fderiv_sq_half {D : ℕ} (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun y => g y ^ 2 / 2) z = g z • fderiv ℝ g z := by
  have he : (fun y => g y ^ 2 / 2) = fun y => (1 / 2 : ℝ) * (g y * g y) := by funext y; ring
  rw [he, HasFDerivAt.fderiv (f := fun y => (1 / 2 : ℝ) * (g y * g y))
    ((hg.hasFDerivAt.mul hg.hasFDerivAt).const_mul (1 / 2 : ℝ))]
  ext u
  simp
  ring

theorem gradDensSymm_thm : GradDensSymmStatement := by
  intro n φ v w U hU hφ z hz
  have hB : ∀ i, (hessC (φ i) z).IsHermitian := fun i =>
    hessC_isHermitian_of_symm _ _
      (((hφ i).contDiffAt (hU.mem_nhds hz)).isSymmSndFDerivAt (by simp))
  unfold gradDens
  rw [gradMat_swap v w z, re_mdisc_cons_conjTranspose _ _ hB]

theorem gradDensNonneg_thm : GradDensNonnegStatement := by
  intro n φ v U hU hφ hl z hz
  have hB : ∀ i, (hessC (φ i) z).PosSemidef := fun i =>
    hessC_posSemidef_of_levi _ _ ((hφ i).contDiffAt (hU.mem_nhds hz)) (hl i z hz)
  unfold gradDens
  rw [gradMat_eq_vecMulVec]
  exact mul_nonneg (by positivity) (re_mdisc_cons_vecMulVec_nonneg _ _ hB)

theorem hessCDz_thm : HessCDzStatement := by
  intro D v U hU hv z hz j k
  have h2 : ContDiffAt ℝ 2 v z := hv.contDiffAt (hU.mem_nhds hz)
  have hL : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc := fun c : Fin D → ℂ =>
    Complex.ofRealCLM.hasFDerivAt.comp z (hL.hasFDerivAt.clm_apply (hasFDerivAt_const c z))
  have hg := ((hc (Pi.single k 1)).add
    ((hc (Complex.I • Pi.single k 1)).const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have hd := hg.congr_of_eventuallyEq (f₁ := dzb k (cplx v))
    (Filter.Eventually.of_forall fun y => by
      rw [dzb_cplx]
      simp only [Pi.add_apply, Function.comp_apply, Complex.ofRealCLM_apply]
      ring)
  rw [dz, hd.fderiv]
  simp only [hessC_eq_leviC, leviC]
  simp
  apply Complex.ext <;> simp <;> ring

theorem gradDensCauchySchwarz_thm : GradDensCauchySchwarzStatement := by
  intro n φ v w U hU hφ hl z hz
  have hB : ∀ i, (hessC (φ i) z).PosSemidef := fun i =>
    hessC_posSemidef_of_levi _ _ ((hφ i).contDiffAt (hU.mem_nhds hz)) (hl i z hz)
  unfold gradDens
  simp only [gradMat_eq_vecMulVec]
  have key : ∀ c X P Q : ℝ, X ^ 2 ≤ P * Q → (c * X) ^ 2 ≤ (c * P) * (c * Q) := by
    intro c X P Q h
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg c)]
  exact key _ _ _ _ (re_mdisc_cons_cs _ _ _ hB)

theorem gradDensLeibniz_thm : GradDensLeibnizStatement := by
  intro n φ f g w z hf hg
  constructor
  · have hM : gradMat (fun y => f y * g y) w z =
        (f z : ℂ) • gradMat g w z + (g z : ℂ) • gradMat f w z := by
      ext j k
      simp only [gradMat, dz_cplx_mul j f g z hf hg, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      ring
    unfold gradDens
    rw [hM, mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · have hM : gradMat g (fun y => g y ^ 2 / 2) z = (g z : ℂ) • gradMat g g z := by
      ext j k
      simp only [gradMat, Matrix.smul_apply, smul_eq_mul, dzb_cplx, fderiv_sq_half g z hg,
        FunLike.coe_smul, Pi.smul_apply]
      push_cast
      ring
    unfold gradDens
    rw [hM, mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring

end Statements

end

end ReciprocityTheory.AnForm.A
