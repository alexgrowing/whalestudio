import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement

noncomputable section

open Complex Matrix

namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity

variable {ι : Type*} [Fintype ι]

theorem quad_smul (A : Matrix ι ι ℝ) (r : ℝ) (x : ι → ℝ) :
    (r • x) ⬝ᵥ (A *ᵥ (r • x)) = r ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem quad_transpose (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_transpose]
  exact dotProduct_comm _ _

theorem norm_inv_smul_mem_sphere {x : ι → ℝ} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem quad_pos_of_sphere (A : Matrix ι ι ℝ)
    (h : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ (A *ᵥ y)) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by
  have h1 := h _ (norm_inv_smul_mem_sphere hx)
  rw [quad_smul] at h1
  have h2 : 0 ≤ ‖x‖⁻¹ ^ 2 := by positivity
  exact pos_of_mul_pos_right h1 h2

theorem sum_sq_le (x : ι → ℝ) : ∑ i, x i ^ 2 ≤ (Fintype.card ι) * ‖x‖ ^ 2 := by
  calc ∑ i, x i ^ 2 ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (Fintype.card ι) * ‖x‖ ^ 2 := by simp

theorem quad_lower {X : Type*} [TopologicalSpace X] (Mf : X → Matrix ι ι ℝ) (hc : Continuous Mf)
    (K : Set X) (hK : IsCompact K) (hpos : ∀ p ∈ K, (Mf p).PosDef) :
    ∃ c > 0, ∀ p ∈ K, ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Mf p *ᵥ x) := by
  classical
  have hF : Continuous (fun q : X × (ι → ℝ) => q.2 ⬝ᵥ (Mf q.1 *ᵥ q.2)) := by
    fun_prop
  have hKS : IsCompact (K ×ˢ Metric.sphere (0 : ι → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  rcases (K ×ˢ Metric.sphere (0 : ι → ℝ) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · exfalso
      have hy : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, norm_inv_smul_mem_sphere hx⟩
      rw [he] at hy
      exact hy
  · obtain ⟨q0, hq0, hmin⟩ := hKS.exists_isMinOn hne hF.continuousOn
    have hq0S : q0.2 ∈ Metric.sphere (0 : ι → ℝ) 1 := hq0.2
    have hne0 : q0.2 ≠ 0 := by
      intro h
      rw [h] at hq0S
      simp at hq0S
    have hmpos : 0 < q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) := by
      have h0 := (Matrix.posDef_iff_dotProduct_mulVec.mp (hpos q0.1 hq0.1)).2 hne0
      simpa using h0
    refine ⟨q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) / (Fintype.card ι + 1), by positivity, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · have hy : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, norm_inv_smul_mem_sphere hx⟩
      have h1 : q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (Mf p *ᵥ (‖x‖⁻¹ • x)) :=
        isMinOn_iff.mp hmin _ hy
      rw [quad_smul] at h1
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h3 : ‖x‖⁻¹ ^ 2 * ‖x‖ ^ 2 = 1 := by field_simp
      have h2 : q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Mf p *ᵥ x) := by
        calc q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) * ‖x‖ ^ 2
            ≤ (‖x‖⁻¹ ^ 2 * (x ⬝ᵥ (Mf p *ᵥ x))) * ‖x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = x ⬝ᵥ (Mf p *ᵥ x) := by
              rw [mul_comm, ← mul_assoc, mul_comm (‖x‖ ^ 2), h3, one_mul]
      have h4 := sum_sq_le x
      have hc1 : (0:ℝ) < Fintype.card ι + 1 := by positivity
      calc q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) / (Fintype.card ι + 1) * ∑ i, x i ^ 2
          ≤ q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) / (Fintype.card ι + 1) * ((Fintype.card ι) * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ q0.2 ⬝ᵥ (Mf q0.1 *ᵥ q0.2) * ‖x‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hc1]
          nlinarith [mul_nonneg hmpos.le (sq_nonneg ‖x‖)]
        _ ≤ _ := h2

theorem symPart_isHermitian (A : Matrix ι ι ℝ) : (A + Aᵀ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [add_comm]

theorem symPart_posDef_of_sphere (A : Matrix ι ι ℝ)
    (h : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ ((A + Aᵀ) *ᵥ y)) : (A + Aᵀ).PosDef := by
  exact Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨symPart_isHermitian A, fun x hx => by simpa using quad_pos_of_sphere _ h x hx⟩

end ReciprocityTheory.PTheta.sphereQuadraticPositivity

namespace ReciprocityTheory.PTheta
open sphereQuadraticPositivity

theorem siegelSubDomain_holds : SiegelSubDomainStatement := by
  unfold SiegelSubDomainStatement ThetaDomain SiegelH
  intro ι _ τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp

theorem domainOpen_holds : DomainOpenStatement := by
  unfold DomainOpenStatement
  intro ι _
  classical
  let Mt : (ι → ι → ℂ) → Matrix ι ι ℝ :=
    fun t => (of t).map Complex.im + ((of t).map Complex.im)ᵀ
  have hc : Continuous Mt := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (Complex.continuous_im.comp ((continuous_apply j).comp (continuous_apply i))).add
      (Complex.continuous_im.comp ((continuous_apply i).comp (continuous_apply j)))
  have hF : Continuous (fun q : (ι → ι → ℂ) × (ι → ℝ) => q.2 ⬝ᵥ (Mt q.1 *ᵥ q.2)) := by
    fun_prop
  have hset : {t : ι → ι → ℂ | of t ∈ ThetaDomain ι} =
      {t | ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ (Mt t *ᵥ y)} := by
    ext t
    constructor
    · intro ht y hy
      have ht' : (Mt t).PosDef := ht
      have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      have h0 := (Matrix.posDef_iff_dotProduct_mulVec.mp ht').2 hy0
      simpa using h0
    · intro ht
      exact symPart_posDef_of_sphere ((of t).map Complex.im) ht
  rw [hset, isOpen_iff_mem_nhds]
  intro t0 ht0
  have hev : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1,
      ∀ᶠ q : (ι → ι → ℂ) × (ι → ℝ) in nhds (t0, y), 0 < q.2 ⬝ᵥ (Mt q.1 *ᵥ q.2) :=
    fun y hy => (hF.tendsto (t0, y)).eventually (lt_mem_nhds (ht0 y hy))
  exact (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
    (P := fun t y => 0 < y ⬝ᵥ (Mt t *ᵥ y)) hev

end ReciprocityTheory.PTheta

namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity

variable {ι : Type*} [Fintype ι]

theorem norm_eC (w : ℂ) : ‖eC w‖ = Real.exp (-2 * Real.pi * w.im) := by
  unfold eC
  rw [Complex.norm_exp]
  congr 1
  simp

theorem shiftVec_eq (a : ι → ℝ) (l : ι → ℤ) :
    shiftVec a l = ofRealVec (fun i => (l i : ℝ) + a i) := by
  funext i
  simp [shiftVec, ofRealVec]

theorem im_ofReal_dot (v : ι → ℝ) (w : ι → ℂ) :
    (ofRealVec v ⬝ᵥ w).im = v ⬝ᵥ (fun i => (w i).im) := by
  simp [dotProduct, ofRealVec, Complex.im_sum]

theorem im_mulVec_ofReal (τ : Matrix ι ι ℂ) (v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec v) i).im) = τ.map Complex.im *ᵥ v := by
  funext i
  simp [mulVec, dotProduct, ofRealVec, Complex.im_sum]

theorem im_arg (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (l : ι → ℤ) :
    (shiftVec a l ⬝ᵥ (τ *ᵥ shiftVec a l) / 2 + shiftVec a l ⬝ᵥ (z + ofRealVec b)).im =
      (fun i => (l i : ℝ) + a i) ⬝ᵥ (τ.map Complex.im *ᵥ (fun i => (l i : ℝ) + a i)) / 2 +
        (fun i => (l i : ℝ) + a i) ⬝ᵥ (fun i => (z i).im) := by
  rw [shiftVec_eq, Complex.add_im, Complex.div_ofNat_im, im_ofReal_dot, im_mulVec_ofReal,
    im_ofReal_dot]
  congr 2
  funext i
  simp [ofRealVec]

theorem coord_bound (β γ k a : ℝ) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    -β * (k + a) ^ 2 + γ * |k + a| ≤ -(β / 4) * k ^ 2 + (γ ^ 2 / (2 * β) + β / 2 * a ^ 2) := by
  have hβ' : β ≠ 0 := hβ.ne'
  have h1 : γ * |k + a| ≤ β / 2 * |k + a| ^ 2 + γ ^ 2 / (2 * β) := by
    have e : β / 2 * |k + a| ^ 2 + γ ^ 2 / (2 * β) - γ * |k + a| =
        (β * |k + a| - γ) ^ 2 / (2 * β) := by
      field_simp
      ring
    have h0 : 0 ≤ (β * |k + a| - γ) ^ 2 / (2 * β) := by positivity
    linarith
  rw [sq_abs] at h1
  have h2 : k ^ 2 ≤ 2 * (k + a) ^ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (k + 2 * a)]
  have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
  nlinarith [h1, h3]

private theorem summable_pi_prod_of_nonneg' {α : Type*} {q : ℕ} (f : Fin q → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin q → α => ∏ i, f i (x i)) := by
  induction q with
  | zero =>
    simp only [Fin.prod_univ_zero]
    exact Summable.of_finite
  | succ q ih =>
    have hs : Summable (fun x : Fin q → α => ∏ i, f i.succ (x i)) :=
      ih (fun (i : Fin q) => f i.succ) (fun (i : Fin q) a => hf0 i.succ a)
        (fun (i : Fin q) => hf i.succ)
    have key : ∀ p : α × (Fin q → α),
        (fun x : Fin (q + 1) → α => ∏ i, f i (x i)) (Fin.consEquiv (fun _ => α) p) =
          f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
      rintro ⟨a, y⟩
      simp [Fin.consEquiv, Fin.prod_univ_succ]
    have hf00 : 0 ≤ f 0 := fun a => hf0 0 a
    have hg0 : 0 ≤ fun y : Fin q → α => ∏ i : Fin q, f i.succ (y i) :=
      fun y => Finset.prod_nonneg fun (i : Fin q) _ => hf0 i.succ (y i)
    have hprod := Summable.mul_of_nonneg (hf 0) hs hf00 hg0
    have hcomp : (fun x : Fin (q + 1) → α => ∏ i, f i (x i)) ∘ (Fin.consEquiv fun _ => α) =
        fun p : α × (Fin q → α) => f 0 p.1 * ∏ i, f i.succ (p.2 i) := funext key
    exact (Equiv.summable_iff (Fin.consEquiv fun _ => α)).mp (by rw [hcomp]; exact hprod)

theorem summable_pi_prod {g : ι → ℤ → ℝ} (hg0 : ∀ i k, 0 ≤ g i k) (hg : ∀ i, Summable (g i)) :
    Summable (fun l : ι → ℤ => ∏ i, g i (l i)) := by
  classical
  let e := Fintype.equivFin ι
  have h := summable_pi_prod_of_nonneg' (fun j k => g (e.symm j) k) (fun j k => hg0 _ _) (fun j => hg _)
  have key : (fun x : Fin (Fintype.card ι) → ℤ => ∏ j, g (e.symm j) (x j)) ∘
      (e.arrowCongr (Equiv.refl ℤ)) = fun l : ι → ℤ => ∏ i, g i (l i) := by
    funext l
    exact Equiv.prod_comp e.symm (fun i => g i (l i))
  rw [← key]
  exact (Equiv.summable_iff _).mpr h

theorem summable_gauss (β C : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => Real.exp (-(β / 4) * (k : ℝ) ^ 2 + C)) := by
  have hτ : 0 < (⟨0, β / (4 * Real.pi)⟩ : ℂ).im := by
    show 0 < β / (4 * Real.pi)
    positivity
  have hs := ((summable_jacobiTheta₂_term_iff 0 _).mpr hτ).norm
  have key : (fun k : ℤ => Real.exp (-(β / 4) * (k : ℝ) ^ 2 + C)) = fun k : ℤ =>
      Real.exp C * ‖jacobiTheta₂_term k 0 (⟨0, β / (4 * Real.pi)⟩ : ℂ)‖ := by
    funext k
    rw [norm_jacobiTheta₂_term, ← Real.exp_add]
    congr 1
    dsimp only
    simp only [Complex.zero_im, mul_zero, sub_zero]
    field_simp
    ring
  rw [key]
  exact hs.mul_left _

end ReciprocityTheory.PTheta.sphereQuadraticPositivity

namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]

theorem term_bound (a b : ι → ℝ) (z : ι → ℂ) (A : Matrix ι ι ℂ) (l : ι → ℤ) (c R : ℝ)
    (hc0 : 0 < c) (hR0 : 0 ≤ R) (hR : ∀ i, |(z i).im| ≤ R)
    (hq : ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ ((A.map Complex.im + (A.map Complex.im)ᵀ) *ᵥ x)) :
    ‖thetaTerm a b z A l‖ ≤ ∏ i, Real.exp (-((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
      ((2 * Real.pi * R) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)) := by
  have hβ : 0 < Real.pi * c / 2 := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ι → ℝ, v = fun i => (l i : ℝ) + a i := ⟨_, rfl⟩
  have hnorm : ‖thetaTerm a b z A l‖ = Real.exp (-2 * Real.pi *
      (v ⬝ᵥ (A.map Complex.im *ᵥ v) / 2 + v ⬝ᵥ (fun i => (z i).im))) := by
    unfold thetaTerm
    rw [norm_eC, im_arg, ← hv]
  rw [hnorm, ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hq2 : c * ∑ i, v i ^ 2 ≤ 2 * (v ⬝ᵥ (A.map Complex.im *ᵥ v)) := by
    have h0 := hq v
    rw [add_mulVec, dotProduct_add, quad_transpose] at h0
    linarith
  have hz : -(v ⬝ᵥ (fun i => (z i).im)) ≤ R * ∑ i, |v i| := by
    rw [Finset.mul_sum, dotProduct, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    show -(v i * (z i).im) ≤ R * |v i|
    have h1 := hR i
    have h2 : -(v i * (z i).im) ≤ |v i| * |(z i).im| := by
      rw [← abs_mul]
      exact neg_le_abs _
    nlinarith [abs_nonneg (v i), mul_le_mul_of_nonneg_left h1 (abs_nonneg (v i))]
  have hcb : ∀ i, -(Real.pi * c / 2) * v i ^ 2 + 2 * Real.pi * R * |v i| ≤
      -((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
        ((2 * Real.pi * R) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2) := by
    intro i
    rw [hv]
    exact coord_bound _ _ _ _ hβ (by positivity)
  calc -2 * Real.pi * (v ⬝ᵥ (A.map Complex.im *ᵥ v) / 2 + v ⬝ᵥ (fun i => (z i).im))
      ≤ ∑ i, (-(Real.pi * c / 2) * v i ^ 2 + 2 * Real.pi * R * |v i|) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        nlinarith [mul_le_mul_of_nonneg_left hq2 Real.pi_pos.le,
          mul_le_mul_of_nonneg_left hz (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    _ ≤ _ := Finset.sum_le_sum fun i _ => hcb i

end ReciprocityTheory.PTheta.sphereQuadraticPositivity

namespace ReciprocityTheory.PTheta
open sphereQuadraticPositivity

theorem thetaMTest_holds : ThetaMTestStatement := by
  intro ι _ a K hK hKd
  classical
  let Mf : (ι → ℂ) × (ι → ι → ℂ) → Matrix ι ι ℝ :=
    fun p => (of p.2).map Complex.im + ((of p.2).map Complex.im)ᵀ
  have hc : Continuous Mf := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (Complex.continuous_im.comp ((continuous_apply j).comp
      ((continuous_apply i).comp continuous_snd))).add
      (Complex.continuous_im.comp ((continuous_apply i).comp
        ((continuous_apply j).comp continuous_snd)))
  obtain ⟨c, hc0, hcK⟩ := quad_lower Mf hc K hK (fun p hp => hKd p hp)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun p => p.1) continuous_fst.continuousOn
  refine ⟨fun l => ∏ i, Real.exp (-((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
      ((2 * Real.pi * max C 0) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)),
    ?_, ?_⟩
  · exact summable_pi_prod (g := fun i k => Real.exp (-((Real.pi * c / 2) / 4) * (k : ℝ) ^ 2 +
      ((2 * Real.pi * max C 0) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)))
      (fun i k => (Real.exp_pos _).le) (fun i => summable_gauss _ _ (by positivity))
  · intro b p hp l
    refine term_bound a b p.1 (of p.2) l c (max C 0) hc0 (le_max_right _ _) (fun i => ?_)
      (fun x => hcK p hp x)
    have h1 : ‖p.1‖ ≤ C := hC p hp
    calc |(p.1 i).im| ≤ ‖p.1 i‖ := Complex.abs_im_le_norm _
      _ ≤ ‖p.1‖ := norm_le_pi_norm p.1 i
      _ ≤ C := h1
      _ ≤ max C 0 := le_max_left _ _

theorem thetaSummable_holds : ThetaSummableStatement := by
  intro ι _ a b z τ hτ
  obtain ⟨u, hu, hb⟩ := thetaMTest_holds ι a {(z, Matrix.of.symm τ)} isCompact_singleton
    (by rintro p rfl; simpa using hτ)
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_) hu
  simpa using hb b (z, Matrix.of.symm τ) rfl l

end ReciprocityTheory.PTheta
