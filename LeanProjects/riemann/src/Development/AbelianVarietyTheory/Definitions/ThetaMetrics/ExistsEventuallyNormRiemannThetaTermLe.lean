import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

open Complex Matrix Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace GlobalTheory

variable {ι κ : Type*}

def IsSiegel (Ω : Matrix ι ι ℂ) : Prop := Ω.IsSymm ∧ (Ω.map Complex.im).PosDef

theorem isSiegel_iff_mem_siegelH [Fintype ι] {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ Ω ∈ ReciprocityTheory.PTheta.SiegelH ι := Iff.rfl

theorem IsSiegel.mk {Ω : Matrix ι ι ℂ} (isSymm : Ω.IsSymm) (posDef : (Ω.map Complex.im).PosDef) :
    IsSiegel Ω := ⟨isSymm, posDef⟩

theorem IsSiegel.isSymm {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) : Ω.IsSymm := h.1

theorem IsSiegel.posDef {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) : (Ω.map Complex.im).PosDef := h.2

theorem IsSiegel.mem_siegelH [Fintype ι] {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    Ω ∈ ReciprocityTheory.PTheta.SiegelH ι := h

theorem IsSiegel.of_mem_siegelH [Fintype ι] {Ω : Matrix ι ι ℂ}
    (h : Ω ∈ ReciprocityTheory.PTheta.SiegelH ι) : IsSiegel Ω := h

def siegelUpperHalfSpace (ι : Type*) : Set (Matrix ι ι ℂ) := {Ω | IsSiegel Ω}

theorem siegelUpperHalfSpace_eq_siegelH (ι : Type*) [Fintype ι] :
    siegelUpperHalfSpace ι = ReciprocityTheory.PTheta.SiegelH ι := rfl

@[simp] theorem mem_siegelUpperHalfSpace {Ω : Matrix ι ι ℂ} :
    Ω ∈ siegelUpperHalfSpace ι ↔ IsSiegel Ω := Iff.rfl

theorem isHermitian_map_im_of_isSymm {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) :
    (Ω.map Complex.im).IsHermitian := by
  ext i j
  simp [conjTranspose_apply, h.apply]

theorem IsSiegel.of_dotProduct_pos [Fintype ι] {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm)
    (hpos : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x)) : IsSiegel Ω :=
  ⟨h, PosDef.of_dotProduct_mulVec_pos (isHermitian_map_im_of_isSymm h)
    fun x hx => by simpa using hpos x hx⟩

theorem IsSiegel.dotProduct_pos [Fintype ι] {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {x : ι → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by
  simpa using h.posDef.dotProduct_mulVec_pos hx

theorem isSiegel_ofReal_add_I_smul {X Y : Matrix ι ι ℝ} (hX : X.IsSymm) (hY : Y.PosDef) :
    IsSiegel (X.map ofReal + I • Y.map ofReal) := by
  have hY' : Y.IsSymm := by
    ext i j
    simpa using hY.isHermitian.apply i j
  refine ⟨?_, ?_⟩
  · ext i j
    simp [hX.apply, hY'.apply]
  · convert hY
    ext i j
    simp

theorem isSiegel_diagonal_iff [DecidableEq ι] {τ : ι → ℂ} :
    IsSiegel (diagonal τ) ↔ ∀ i, 0 < (τ i).im := by
  have : (diagonal τ).map Complex.im = diagonal fun i => (τ i).im := diagonal_map (by simp)
  refine ⟨fun h => ?_, fun h => ⟨isSymm_diagonal _, ?_⟩⟩
  · simpa [this] using h.posDef
  · simpa [this] using h

theorem isSiegel_I_smul_one [DecidableEq ι] : IsSiegel (I • (1 : Matrix ι ι ℂ)) := by
  rw [smul_one_eq_diagonal, isSiegel_diagonal_iff]
  simp

theorem isSiegel_unique_iff [Unique ι] {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ 0 < (Ω default default).im := by
  classical
  have : Ω = diagonal fun _ => Ω default default := by
    ext i j
    obtain rfl := Subsingleton.elim i default
    obtain rfl := Subsingleton.elim j default
    simp
  rw [this, isSiegel_diagonal_iff]
  simp

theorem IsSiegel.smul {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℝ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by
  refine ⟨h.isSymm.smul _, ?_⟩
  convert h.posDef.smul hq using 1
  ext i j
  simp

theorem IsSiegel.natCast_smul {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {q : ℕ} (hq : 0 < q) :
    IsSiegel ((q : ℂ) • Ω) := by
  simpa using h.smul (q := q) (by exact_mod_cast hq)

theorem IsSiegel.submatrix {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {e : κ → ι}
    (he : Function.Injective e) : IsSiegel (Ω.submatrix e e) :=
  ⟨h.isSymm.submatrix e, h.posDef.submatrix he⟩

theorem isSiegel_fromBlocks_iff [Finite ι] [Finite κ] {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} :
    IsSiegel (fromBlocks Ω₁ 0 0 Ω₂) ↔ IsSiegel Ω₁ ∧ IsSiegel Ω₂ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  refine ⟨fun h => ⟨h.submatrix Sum.inl_injective, h.submatrix Sum.inr_injective⟩,
    fun ⟨h₁, h₂⟩ => IsSiegel.of_dotProduct_pos ?_ fun x hx => ?_⟩
  · exact IsSymm.fromBlocks h₁.isSymm (by simp) h₂.isSymm
  · have e : x ⬝ᵥ ((fromBlocks Ω₁ 0 0 Ω₂).map Complex.im *ᵥ x) =
        (x ∘ Sum.inl) ⬝ᵥ (Ω₁.map Complex.im *ᵥ (x ∘ Sum.inl)) +
        (x ∘ Sum.inr) ⬝ᵥ (Ω₂.map Complex.im *ᵥ (x ∘ Sum.inr)) := by
      simp [dotProduct, mulVec, Fintype.sum_sum_type]
    have n₁ := h₁.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have n₂ := h₂.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    simp only [star_trivial] at n₁ n₂
    rw [e]
    by_cases hl : x ∘ Sum.inl = 0
    · have hr : x ∘ Sum.inr ≠ 0 := fun hr => hx (by
        funext i
        rcases i with i | i
        · exact congrFun hl i
        · exact congrFun hr i)
      linarith [h₂.dotProduct_pos hr]
    · linarith [h₁.dotProduct_pos hl]

theorem isSiegel_example : IsSiegel !![1 + 2 * I, 1 / 2 + I; 1 / 2 + I, 2 * I] := by
  refine IsSiegel.of_dotProduct_pos ?_ fun x hx => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by funext i; fin_cases i <;> simp [h.1, h.2])
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    rcases this with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]

variable [Fintype ι] [Fintype κ]

theorem posDef_exists_mul_dotProduct_le {Y : Matrix ι ι ℝ} (hY : Y.PosDef) :
    ∃ c > 0, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
  have hc : Continuous fun x : ι → ℝ => x ⬝ᵥ (Y *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨c, hc0, hcl⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_forall_le' hc.continuousOn
    (a := 0) (fun x hx => by
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      simpa using hY.dotProduct_mulVec_pos hx0)
  refine ⟨c / (Fintype.card ι + 1), by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 := hcl (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
  have h2 : c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
    refine this.trans_eq ?_
    field_simp
  have h3 : x ⬝ᵥ x ≤ (Fintype.card ι + 1) * ‖x‖ ^ 2 := by
    have : x ⬝ᵥ x ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      rw [← sq, ← sq_abs]
      gcongr
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    nlinarith [sq_nonneg ‖x‖]
  calc c / (Fintype.card ι + 1) * (x ⬝ᵥ x) ≤ c / (Fintype.card ι + 1) *
        ((Fintype.card ι + 1) * ‖x‖ ^ 2) := by gcongr
    _ = c * ‖x‖ ^ 2 := by field_simp
    _ ≤ _ := h2

theorem IsSiegel.exists_eventually_mul_dotProduct_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    ∃ c > 0, ∀ᶠ Ω' in 𝓝 Ω, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Matrix.map Ω' Complex.im *ᵥ x) := by
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
  set N : ℝ := Fintype.card ι + 1 with hN
  have hN0 : 0 < N := by positivity
  refine ⟨c / 2, by positivity, ?_⟩
  have hev : ∀ᶠ Ω' in 𝓝 Ω, ∀ i j, |(Ω' i j).im - (Ω i j).im| < c / (2 * N) := by
    simp only [eventually_all]
    intro i j
    have hc' : Continuous fun Ω' : Matrix ι ι ℂ => |(Ω' i j).im - (Ω i j).im| := by
      have : Continuous fun Ω' : Matrix ι ι ℂ => Ω' i j := continuous_id.matrix_elem i j
      fun_prop
    exact hc'.continuousAt.eventually_lt continuousAt_const (by simp; positivity)
  filter_upwards [hev] with Ω' hΩ' x
  have h1 : x ⬝ᵥ (Ω.map Complex.im *ᵥ x) - x ⬝ᵥ (Matrix.map Ω' Complex.im *ᵥ x) ≤
      ∑ i, ∑ j, c / (2 * N) * ((x i * x i + x j * x j) / 2) := by
    simp only [dotProduct, mulVec, map_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    obtain ⟨l, r⟩ := abs_lt.mp (hΩ' i j)
    nlinarith [mul_nonneg (sub_nonneg.mpr l.le) (sq_nonneg (x i - x j)),
      mul_nonneg (sub_nonneg.mpr r.le) (sq_nonneg (x i + x j))]
  have h2 : ∑ i, ∑ j, c / (2 * N) * ((x i * x i + x j * x j) / 2) =
      c / (2 * N) * (Fintype.card ι * (x ⬝ᵥ x)) := by
    simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, dotProduct]
    simp only [mul_left_comm (x _) (Fintype.card ι : ℝ), ← Finset.mul_sum]
    ring
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h3 : c / (2 * N) * (Fintype.card ι * (x ⬝ᵥ x)) ≤ c / 2 * (x ⬝ᵥ x) := by
    calc _ ≤ c / (2 * N) * (N * (x ⬝ᵥ x)) := by gcongr; linarith
      _ = _ := by field_simp
  linarith [hY x]

theorem IsSiegel.eventually_isSiegel {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    ∀ᶠ Ω' in 𝓝 Ω, Matrix.IsSymm Ω' → IsSiegel Ω' := by
  obtain ⟨c, hc, hY⟩ := h.exists_eventually_mul_dotProduct_le
  filter_upwards [hY] with Ω' hΩ' hs
  refine IsSiegel.of_dotProduct_pos hs fun x hx => lt_of_lt_of_le (mul_pos hc ?_) (hΩ' x)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

def riemannThetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) : ℂ :=
  ReciprocityTheory.PTheta.thetaTerm a b v Ω n

theorem riemannThetaTerm_eq_thetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n = ReciprocityTheory.PTheta.thetaTerm a b v Ω n := rfl

theorem riemannThetaTerm_def (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n =
      cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) := rfl

attribute [eqns riemannThetaTerm_def] riemannThetaTerm

def riemannTheta (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  ReciprocityTheory.PTheta.theta a b v Ω

theorem riemannTheta_eq_theta (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω v = ReciprocityTheory.PTheta.theta a b v Ω := rfl

theorem riemannTheta_def (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω v = ∑' n : ι → ℤ, riemannThetaTerm a b Ω v n := rfl

attribute [eqns riemannTheta_def] riemannTheta

theorem riemannThetaTerm_eq_sum (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n =
      cexp (π * I * (∑ i, ∑ j, ((n i : ℂ) + a i) * Ω i j * ((n j : ℂ) + a j)) +
        2 * π * I * ∑ i, ((n i : ℂ) + a i) * (v i + b i)) := by
  simp only [riemannThetaTerm_def, dotProduct, mulVec, Finset.mul_sum _ _ ((n _ : ℂ) + a _),
    ← mul_assoc]
  congr 1
  ring

theorem riemannThetaTerm_zero_zero (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm 0 0 Ω v n =
      cexp (2 * π * I * (((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))) / 2 +
        (fun i => (n i : ℂ)) ⬝ᵥ v)) := by
  simp [riemannThetaTerm_def]

theorem riemannThetaTerm_ne_zero (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n ≠ 0 := Complex.exp_ne_zero _

theorem norm_riemannThetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    ‖riemannThetaTerm a b Ω v n‖ =
      Real.exp (-π * ((fun i => (n i : ℝ) + a i) ⬝ᵥ (Ω.map Complex.im *ᵥ fun i => (n i : ℝ) + a i))
        - 2 * π * ((fun i => (n i : ℝ) + a i) ⬝ᵥ fun i => (v i).im)) := by
  rw [riemannThetaTerm_def, Complex.norm_exp]
  congr 1
  simp [dotProduct, mulVec, Finset.mul_sum _ _ ((n _ : ℂ) + a _),
    Finset.mul_sum _ _ ((n _ : ℝ) + a _)]
  ring

def riemannThetaBound (a : ι → ℝ) (c S : ℝ) (n : ι → ℤ) : ℝ :=
  Real.exp (-π * (c * ((fun i => (n i : ℝ) + a i) ⬝ᵥ fun i => (n i : ℝ) + a i) -
    2 * S * ∑ i, |(n i : ℝ) + a i|))

theorem riemannThetaBound_pos (a : ι → ℝ) (c S : ℝ) (n : ι → ℤ) :
    0 < riemannThetaBound a c S n := Real.exp_pos _

theorem norm_riemannThetaTerm_le (a b : ι → ℝ) {Ω : Matrix ι ι ℂ} {v : ι → ℂ} {c S : ℝ}
    (hΩ : ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Ω.map Complex.im *ᵥ x)) (hv : ∀ i, |(v i).im| ≤ S)
    (n : ι → ℤ) : ‖riemannThetaTerm a b Ω v n‖ ≤ riemannThetaBound a c S n := by
  rw [norm_riemannThetaTerm, riemannThetaBound, Real.exp_le_exp]
  have h1 := hΩ fun i => (n i : ℝ) + a i
  have h2 : -((fun i => (n i : ℝ) + a i) ⬝ᵥ fun i => (v i).im) ≤ S * ∑ i, |(n i : ℝ) + a i| := by
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => (neg_le_abs _).trans ?_
    rw [abs_mul, mul_comm]
    gcongr
    exact hv i
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]

theorem summable_pi_prod_of_nonneg {α : ι → Type*} {f : ∀ i, α i → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image (· i), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          fun n _ _ => Finset.prod_nonneg fun i _ => h0 i _
    _ = ∏ i, ∑ x ∈ s.image (· i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

theorem summable_exp_neg_shifted_sq (a S : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-π * (c * ((n + a) * (n + a)) - 2 * S * |n + a|)) := by
  have := (summable_pow_mul_jacobiTheta₂_term_bound (|S| + c * |a|) hc 0).mul_left
    (Real.exp (2 * π * |S| * |a|))
  refine this.of_nonneg_of_le (fun n => (Real.exp_pos _).le) fun n => ?_
  rw [pow_zero, one_mul, ← Real.exp_add, Real.exp_le_exp, Int.cast_abs]
  have h1 : S * |n + a| ≤ |S| * (|(n : ℝ)| + |a|) :=
    mul_le_mul (le_abs_self S) (abs_add_le _ _) (abs_nonneg _) (abs_nonneg _)
  have h2 : -((n : ℝ) * a) ≤ |(n : ℝ)| * |a| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h3 : c * (n ^ 2 - 2 * (|(n : ℝ)| * |a|)) ≤ c * ((n + a) * (n + a)) := by
    gcongr
    nlinarith [sq_nonneg a]
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h3 Real.pi_pos.le]

theorem summable_riemannThetaBound (a : ι → ℝ) {c : ℝ} (hc : 0 < c) (S : ℝ) :
    Summable (riemannThetaBound a c S) := by
  refine (summable_pi_prod_of_nonneg (fun i x => (Real.exp_pos _).le)
    fun i => summable_exp_neg_shifted_sq (a i) S hc).congr fun n => ?_
  rw [riemannThetaBound, ← Real.exp_sum]
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem summable_pow_mul_riemannThetaBound (a : ι → ℝ) {c : ℝ} (hc : 0 < c) (S : ℝ) (k : ℕ) :
    Summable fun n : ι → ℤ => (∑ i, |(n i : ℝ) + a i|) ^ k * riemannThetaBound a c S n := by
  refine ((summable_riemannThetaBound a hc (S + 1 / (2 * π))).mul_left
    (k.factorial : ℝ)).of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (riemannThetaBound_pos ..).le) fun n => ?_
  have h0 : 0 ≤ ∑ i, |(n i : ℝ) + a i| := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ h0 k
  rw [div_le_iff₀' (by positivity)] at h1
  have h2 : riemannThetaBound a c (S + 1 / (2 * π)) n =
      Real.exp (∑ i, |(n i : ℝ) + a i|) * riemannThetaBound a c S n := by
    rw [riemannThetaBound, riemannThetaBound, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h1 (riemannThetaBound_pos ..).le

theorem abs_im_apply_le_norm (v : ι → ℂ) (i : ι) : |(v i).im| ≤ ‖v‖ :=
  (Complex.abs_im_le_norm _).trans (norm_le_pi_norm v i)

theorem IsSiegel.summable_norm_riemannThetaTerm {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : Summable fun n => ‖riemannThetaTerm a b Ω v n‖ := by
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
  exact (summable_riemannThetaBound a hc ‖v‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_riemannThetaTerm_le a b hY (abs_im_apply_le_norm v))

theorem IsSiegel.summable_riemannThetaTerm {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : Summable (riemannThetaTerm a b Ω v) :=
  (h.summable_norm_riemannThetaTerm a b v).of_norm

theorem IsSiegel.hasSum_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : HasSum (riemannThetaTerm a b Ω v) (riemannTheta a b Ω v) :=
  (h.summable_riemannThetaTerm a b v).hasSum

theorem IsSiegel.exists_eventually_norm_riemannThetaTerm_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ c > 0, ∃ S, ∀ᶠ p : (ι → ℂ) × Matrix ι ι ℂ in 𝓝 (v, Ω),
      ∀ n, ‖riemannThetaTerm a b p.2 p.1 n‖ ≤ riemannThetaBound a c S n := by
  obtain ⟨c, hc, hY⟩ := h.exists_eventually_mul_dotProduct_le
  refine ⟨c, hc, ‖v‖ + 1, ?_⟩
  have h1 : ∀ᶠ w : ι → ℂ in 𝓝 v, ‖w‖ < ‖v‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [h1.prod_nhds hY] with p hp n
  exact norm_riemannThetaTerm_le a b hp.2 (fun i => (abs_im_apply_le_norm _ i).trans hp.1.le) n

theorem hasSumLocallyUniformlyOn_riemannTheta (a b : ι → ℝ) :
    HasSumLocallyUniformlyOn
      (fun n (p : (ι → ℂ) × Matrix ι ι ℂ) => riemannThetaTerm a b p.2 p.1 n)
      (fun p => riemannTheta a b p.2 p.1) (Set.univ ×ˢ ReciprocityTheory.PTheta.SiegelH ι) := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun p hp => ?_
  obtain ⟨c, hc, S, hS⟩ := IsSiegel.exists_eventually_norm_riemannThetaTerm_le hp.2 a b p.1
  refine ⟨_, mem_nhdsWithin_of_mem_nhds hS, ?_⟩
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  exact tendstoUniformlyOn_tsum (summable_riemannThetaBound a hc S) fun n q hq => hq n

theorem IsSiegel.hasSumLocallyUniformly_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) :
    HasSumLocallyUniformly (fun n v => riemannThetaTerm a b Ω v n) (riemannTheta a b Ω) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly, ← tendstoLocallyUniformlyOn_univ]
  exact (hasSumLocallyUniformlyOn_riemannTheta a b).comp (t := Set.univ) (fun v => (v, Ω))
    (fun v _ => ⟨trivial, h⟩) (by fun_prop)

theorem continuous_riemannThetaTerm (a b : ι → ℝ) (n : ι → ℤ) :
    Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannThetaTerm a b p.2 p.1 n := by
  have (i j : ι) : Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ => p.2 i j :=
    continuous_snd.matrix_elem i j
  simp only [riemannThetaTerm_eq_sum]
  fun_prop

theorem continuousOn_riemannTheta (a b : ι → ℝ) :
    ContinuousOn (fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannTheta a b p.2 p.1)
      (Set.univ ×ˢ ReciprocityTheory.PTheta.SiegelH ι) :=
  TendstoLocallyUniformlyOn.continuousOn (hasSumLocallyUniformlyOn_riemannTheta a b)
    (Frequently.of_forall fun s =>
      (continuous_finsetSum s fun n _ => continuous_riemannThetaTerm a b n).continuousOn)

def riemannThetaForm (a : ι → ℝ) (n : ι → ℤ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (2 * π * I * ((n i : ℂ) + a i)) • ContinuousLinearMap.proj i

@[simp] theorem riemannThetaForm_apply (a : ι → ℝ) (n : ι → ℤ) (w : ι → ℂ) :
    riemannThetaForm a n w = 2 * π * I * ((fun i => (n i : ℂ) + a i) ⬝ᵥ w) := by
  simp [riemannThetaForm, dotProduct, Finset.mul_sum, mul_assoc]

theorem norm_riemannThetaForm_le (a : ι → ℝ) (n : ι → ℤ) :
    ‖riemannThetaForm a n‖ ≤ 2 * π * ∑ i, |(n i : ℝ) + a i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [riemannThetaForm_apply, norm_mul, mul_assoc (2 * π), Finset.sum_mul]
  refine mul_le_mul (by simp [abs_of_pos Real.pi_pos]) ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)) (norm_nonneg _) (by positivity)
  rw [norm_mul, ← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  gcongr
  exact norm_le_pi_norm w i

theorem hasFDerivAt_riemannThetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    HasFDerivAt (fun w => riemannThetaTerm a b Ω w n)
      (riemannThetaTerm a b Ω v n • riemannThetaForm a n) v := by
  have e (w : ι → ℂ) : riemannThetaTerm a b Ω w n =
      cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => (b i : ℂ)) + riemannThetaForm a n w) := by
    rw [riemannThetaTerm_def, riemannThetaForm_apply]
    congr 1
    simp only [dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  simp only [e]
  exact ((riemannThetaForm a n).hasFDerivAt.const_add _).cexp

theorem IsSiegel.summable_norm_riemannThetaTerm_smul_form {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    Summable fun n => ‖riemannThetaTerm a b Ω v n • riemannThetaForm a n‖ := by
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
  refine ((summable_pow_mul_riemannThetaBound a hc ‖v‖ 1).mul_left (2 * π)).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  rw [norm_smul, pow_one, ← mul_assoc, mul_comm]
  exact mul_le_mul (norm_riemannThetaForm_le a n)
    (norm_riemannThetaTerm_le a b hY (abs_im_apply_le_norm v) n) (norm_nonneg _) (by positivity)

theorem IsSiegel.hasFDerivAt_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    HasFDerivAt (riemannTheta a b Ω)
      (∑' n, riemannThetaTerm a b Ω v n • riemannThetaForm a n) v := by
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le h.posDef
  have hv : v ∈ Metric.ball (0 : ι → ℂ) (‖v‖ + 1) := by simp
  refine hasFDerivAt_tsum_of_isPreconnected
    (f := fun n w => riemannThetaTerm a b Ω w n)
    (f' := fun n w => riemannThetaTerm a b Ω w n • riemannThetaForm a n)
    ((summable_pow_mul_riemannThetaBound a hc (‖v‖ + 1) 1).mul_left (2 * π))
    Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun n w _ => hasFDerivAt_riemannThetaTerm a b Ω w n) (fun n w hw => ?_) hv
    (h.summable_riemannThetaTerm a b v) hv
  rw [norm_smul, pow_one, ← mul_assoc, mul_comm]
  refine mul_le_mul (norm_riemannThetaForm_le a n)
    (norm_riemannThetaTerm_le a b hY (fun i => (abs_im_apply_le_norm w i).trans ?_) n)
    (norm_nonneg _) (by positivity)
  exact (mem_ball_zero_iff.mp hw).le

theorem IsSiegel.differentiable_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) : Differentiable ℂ (riemannTheta a b Ω) :=
  fun v => (h.hasFDerivAt_riemannTheta a b v).differentiableAt

theorem IsSiegel.continuous_riemannTheta {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) : Continuous (riemannTheta a b Ω) :=
  (h.differentiable_riemannTheta a b).continuous

theorem cexp_two_pi_I_dotProduct_intCast (n m : ι → ℤ) :
    cexp (2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (m i : ℂ))) = 1 := by
  have : ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (m i : ℂ)) = ((n ⬝ᵥ m : ℤ) : ℂ) := by
    simp [dotProduct]
  rw [this, mul_comm, Complex.exp_int_mul_two_pi_mul_I]

theorem dotProduct_mulVec_comm_of_isSymm {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (u w : ι → ℂ) :
    u ⬝ᵥ (Ω *ᵥ w) = w ⬝ᵥ (Ω *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, h.eq, dotProduct_comm]

theorem riemannThetaTerm_add_ofReal (a b x : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + fun i => (x i : ℂ)) n = riemannThetaTerm a (b + x) Ω v n := by
  simp only [riemannThetaTerm_def, Pi.add_apply, ofReal_add, add_assoc, add_comm (x _ : ℂ)]

theorem riemannTheta_add_ofReal (a b x : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω (v + fun i => (x i : ℂ)) = riemannTheta a (b + x) Ω v := by
  simp only [riemannTheta_def, riemannThetaTerm_add_ofReal]

theorem riemannThetaTerm_add (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v w : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + w) n =
      riemannThetaTerm a b Ω v n * cexp (2 * π * I * ((fun i => (n i : ℂ) + a i) ⬝ᵥ w)) := by
  rw [riemannThetaTerm_def, riemannThetaTerm_def, ← Complex.exp_add]
  congr 1
  have : (fun i => (v + w) i + (b i : ℂ)) = (fun i => v i + b i) + w := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [this, dotProduct_add]
  ring

theorem riemannThetaTerm_add_intCast (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (m n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + fun i => (m i : ℂ)) n =
      cexp (2 * π * I * ((fun i => (a i : ℂ)) ⬝ᵥ fun i => (m i : ℂ))) *
        riemannThetaTerm a b Ω v n := by
  have : (fun i => (n i : ℂ) + a i) = (fun i => (n i : ℂ)) + fun i => (a i : ℂ) := rfl
  rw [riemannThetaTerm_add, this, add_dotProduct, mul_add, Complex.exp_add,
    cexp_two_pi_I_dotProduct_intCast, one_mul, mul_comm]

theorem riemannTheta_add_intCast (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (m : ι → ℤ) :
    riemannTheta a b Ω (v + fun i => (m i : ℂ)) =
      cexp (2 * π * I * ((fun i => (a i : ℂ)) ⬝ᵥ fun i => (m i : ℂ))) * riemannTheta a b Ω v := by
  simp only [riemannTheta_def, riemannThetaTerm_add_intCast, tsum_mul_left]

theorem riemannThetaTerm_add_mulVec_ofReal {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b y : ι → ℝ)
    (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (v + Ω *ᵥ fun i => (y i : ℂ)) n =
      cexp (-(2 * π * I) * (((fun i => (y i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (y i : ℂ))) / 2 +
        (fun i => (y i : ℂ)) ⬝ᵥ fun i => v i + b i)) * riemannThetaTerm (a + y) b Ω v n := by
  have : (fun i => (n i : ℂ) + ((a + y) i : ℝ)) =
      (fun i => (n i : ℂ) + a i) + fun i => (y i : ℂ) := by
    funext i
    simp [add_assoc]
  rw [riemannThetaTerm_add, riemannThetaTerm_def, riemannThetaTerm_def, this, ← Complex.exp_add,
    ← Complex.exp_add, mulVec_add, add_dotProduct, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_mulVec_comm_of_isSymm h (fun i => (y i : ℂ)) fun i => (n i : ℂ) + a i]
  congr 1
  ring

theorem riemannTheta_add_mulVec_ofReal {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b y : ι → ℝ)
    (v : ι → ℂ) :
    riemannTheta a b Ω (v + Ω *ᵥ fun i => (y i : ℂ)) =
      cexp (-(2 * π * I) * (((fun i => (y i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (y i : ℂ))) / 2 +
        (fun i => (y i : ℂ)) ⬝ᵥ fun i => v i + b i)) * riemannTheta (a + y) b Ω v := by
  simp only [riemannTheta_def, riemannThetaTerm_add_mulVec_ofReal h, tsum_mul_left]

theorem riemannThetaTerm_char_add_intCast (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ)
    (k n : ι → ℤ) :
    riemannThetaTerm (a + fun i => (k i : ℝ)) b Ω v n = riemannThetaTerm a b Ω v (n + k) := by
  have : (fun i => (n i : ℂ) + ((a + fun i => (k i : ℝ)) i : ℝ)) =
      fun i => ((n + k) i : ℂ) + a i := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [riemannThetaTerm_def, riemannThetaTerm_def, this]

theorem riemannTheta_char_add_intCast_left (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ)
    (k : ι → ℤ) : riemannTheta (a + fun i => (k i : ℝ)) b Ω v = riemannTheta a b Ω v := by
  simp only [riemannTheta_def, riemannThetaTerm_char_add_intCast]
  exact (Equiv.addRight k).tsum_eq (riemannThetaTerm a b Ω v)

theorem riemannTheta_char_add_intCast_right (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ)
    (m : ι → ℤ) : riemannTheta a (b + fun i => (m i : ℝ)) Ω v =
      cexp (2 * π * I * ((fun i => (a i : ℂ)) ⬝ᵥ fun i => (m i : ℂ))) * riemannTheta a b Ω v := by
  rw [← riemannTheta_add_ofReal, ← riemannTheta_add_intCast]
  simp

theorem riemannTheta_add_mulVec_intCast {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b : ι → ℝ)
    (v : ι → ℂ) (k : ι → ℤ) :
    riemannTheta a b Ω (v + Ω *ᵥ fun i => (k i : ℂ)) =
      cexp (-(2 * π * I) * (((fun i => (k i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (k i : ℂ))) / 2 +
        (fun i => (k i : ℂ)) ⬝ᵥ fun i => v i + b i)) * riemannTheta a b Ω v := by
  have := riemannTheta_add_mulVec_ofReal h a b (fun i => (k i : ℝ)) v
  rw [riemannTheta_char_add_intCast_left] at this
  simpa only [ofReal_intCast] using this

theorem riemannTheta_add_lattice {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b : ι → ℝ)
    (v : ι → ℂ) (m k : ι → ℤ) :
    riemannTheta a b Ω (v + ((fun i => (m i : ℂ)) + Ω *ᵥ fun i => (k i : ℂ))) =
      cexp (2 * π * I * (((fun i => (a i : ℂ)) ⬝ᵥ fun i => (m i : ℂ)) -
        ((fun i => (b i : ℂ)) ⬝ᵥ fun i => (k i : ℂ)) -
        ((fun i => (k i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (k i : ℂ))) / 2 - (fun i => (k i : ℂ)) ⬝ᵥ v)) *
        riemannTheta a b Ω v := by
  have : (fun i => v i + (b i : ℂ)) = v + fun i => (b i : ℂ) := rfl
  rw [add_comm (fun i => (m i : ℂ)), ← add_assoc, riemannTheta_add_intCast,
    riemannTheta_add_mulVec_intCast h, ← mul_assoc, ← Complex.exp_add, this, dotProduct_add,
    dotProduct_comm (fun i => (k i : ℂ)) fun i => (b i : ℂ)]
  congr 2
  ring

theorem riemannTheta_eq_cexp_mul_zero_zero {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b : ι → ℝ)
    (v : ι → ℂ) :
    riemannTheta a b Ω v =
      cexp (2 * π * I * (((fun i => (a i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (a i : ℂ))) / 2 +
        (fun i => (a i : ℂ)) ⬝ᵥ fun i => v i + b i)) *
        riemannTheta 0 0 Ω (v + (fun i => (b i : ℂ)) + Ω *ᵥ fun i => (a i : ℂ)) := by
  rw [riemannTheta_add_mulVec_ofReal h, riemannTheta_add_ofReal, ← mul_assoc, ← Complex.exp_add]
  simp

theorem riemannThetaTerm_neg (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω (-v) (-n) = riemannThetaTerm (-a) (-b) Ω v n := by
  have e₁ : (fun i => ((-n) i : ℂ) + a i) = -fun i => (n i : ℂ) + ((-a) i : ℝ) := by
    funext i
    simp [add_comm]
  have e₂ : (fun i => (-v) i + (b i : ℂ)) = -fun i => v i + ((-b) i : ℝ) := by
    funext i
    simp [add_comm]
  rw [riemannThetaTerm_def, riemannThetaTerm_def, e₁, e₂, mulVec_neg, neg_dotProduct_neg,
    neg_dotProduct_neg]

theorem riemannTheta_neg (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω (-v) = riemannTheta (-a) (-b) Ω v := by
  simp only [riemannTheta_def, ← riemannThetaTerm_neg]
  exact ((Equiv.neg (ι → ℤ)).tsum_eq (riemannThetaTerm a b Ω (-v))).symm

theorem riemannTheta_zero_zero_neg (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta 0 0 Ω (-v) = riemannTheta 0 0 Ω v := by
  rw [riemannTheta_neg, neg_zero]

theorem riemannTheta_half_neg (α β : ι → ℤ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta (fun i => (α i : ℝ) / 2) (fun i => (β i : ℝ) / 2) Ω (-v) =
      (-1) ^ (α ⬝ᵥ β) * riemannTheta (fun i => (α i : ℝ) / 2) (fun i => (β i : ℝ) / 2) Ω v := by
  have e (γ : ι → ℤ) : (-fun i => (γ i : ℝ) / 2) =
      (fun i => (γ i : ℝ) / 2) + fun i => (((-γ) i : ℤ) : ℝ) := by
    funext i
    simp only [Pi.add_apply, Pi.neg_apply]
    push_cast
    ring
  rw [riemannTheta_neg, e, e, riemannTheta_char_add_intCast_left,
    riemannTheta_char_add_intCast_right]
  congr 1
  have : ((-1 : ℂ)) ^ (α ⬝ᵥ β) = cexp (((α ⬝ᵥ β : ℤ) : ℂ) * -(π * I)) := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  rw [this]
  congr 1
  simp only [dotProduct, Finset.mul_sum, Finset.sum_mul, Pi.neg_apply]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integral_Icc_cexp_dotProduct [DecidableEq ι] (m : ι → ℤ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1,
      cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · simp [hm, measureReal_def, Real.volume_Icc_pi]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
    have e (x : ι → ℝ) : cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) =
        ∏ j, (fun (j : ι) (t : ℝ) => cexp (2 * π * I * m j * t)) j (x j) := by
      simp only [← Complex.exp_sum, dotProduct, Finset.mul_sum, mul_assoc]
    simp only [e]
    rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi,
      integral_fintype_prod_eq_prod (fun (j : ι) (t : ℝ) => cexp (2 * π * I * m j * t))]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have hc : 2 * π * I * m i ≠ 0 := mul_ne_zero two_pi_I_ne_zero (by exact_mod_cast hi)
    rw [Pi.zero_apply, Pi.one_apply, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, integral_exp_mul_complex hc]
    simp [mul_comm _ (m i : ℂ), Complex.exp_int_mul_two_pi_mul_I]

theorem integral_Icc_tsum_mul_cexp {c : (ι → ℤ) → ℂ} (hc : Summable fun m => ‖c m‖) (n : ι → ℤ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1,
      (∑' m, c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))) *
        cexp (-(2 * π * I) * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) = c n := by
  classical
  have e (m : ι → ℤ) (x : ι → ℝ) :
      c m * cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) *
        cexp (-(2 * π * I) * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) =
      c m * cexp (2 * π * I * ((fun i => ((m - n) i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) := by
    have : (fun i => ((m - n) i : ℂ)) = (fun i => (m i : ℂ)) - fun i => (n i : ℂ) := by
      funext i
      simp
    rw [mul_assoc, ← Complex.exp_add, this, sub_dotProduct]
    congr 2
    ring
  have hn (m : ι → ℤ) (x : ι → ℝ) :
      ‖c m * cexp (2 * π * I * ((fun i => ((m - n) i : ℂ)) ⬝ᵥ fun i => (x i : ℂ)))‖ = ‖c m‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp [dotProduct]
  simp only [← tsum_mul_right, e]
  rw [← integral_tsum_of_summable_integral_norm]
  · simp only [integral_const_mul, integral_Icc_cexp_dotProduct, sub_eq_zero, mul_ite, mul_one,
      mul_zero, tsum_ite_eq]
  · intro m
    refine Continuous.integrableOn_Icc ?_
    simp only [dotProduct]
    fun_prop
  · simp only [hn, integral_const, smul_eq_mul]
    exact hc.mul_left _

theorem riemannTheta_add_ofReal_eq_tsum (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (x : ι → ℝ) :
    riemannTheta a b Ω (v + fun i => (x i : ℂ)) =
      cexp (2 * π * I * ((fun i => (a i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) *
        ∑' m, riemannThetaTerm a b Ω v m *
          cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ fun i => (x i : ℂ))) := by
  rw [riemannTheta_def, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have : (fun i => (m i : ℂ) + a i) = (fun i => (m i : ℂ)) + fun i => (a i : ℂ) := rfl
  rw [riemannThetaTerm_add, this, add_dotProduct, mul_add, Complex.exp_add]
  ring

theorem IsSiegel.integral_riemannTheta_mul_cexp {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) (n : ι → ℤ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, riemannTheta a b Ω (v + fun i => (x i : ℂ)) *
        cexp (-(2 * π * I) * ((fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => (x i : ℂ))) =
      riemannThetaTerm a b Ω v n := by
  rw [← integral_Icc_tsum_mul_cexp (h.summable_norm_riemannThetaTerm a b v) n]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : (fun i => (n i : ℂ) + a i) = (fun i => (n i : ℂ)) + fun i => (a i : ℂ) := rfl
  simp only
  rw [riemannTheta_add_ofReal_eq_tsum, this, add_dotProduct, mul_add, Complex.exp_add,
    mul_comm (cexp _) (tsum _), mul_assoc, mul_left_comm (cexp _), ← Complex.exp_add]
  simp

theorem IsSiegel.exists_riemannTheta_add_ofReal_ne_zero {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) :
    ∃ x ∈ Set.Icc (0 : ι → ℝ) 1, riemannTheta a b Ω (v + fun i => (x i : ℂ)) ≠ 0 := by
  by_contra! H
  refine riemannThetaTerm_ne_zero a b Ω v 0 ?_
  rw [← h.integral_riemannTheta_mul_cexp a b v 0]
  exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [H x hx, zero_mul]

theorem IsSiegel.riemannTheta_ne_zero {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) (a b : ι → ℝ) :
    riemannTheta a b Ω ≠ 0 := by
  obtain ⟨x, -, hx⟩ := h.exists_riemannTheta_add_ofReal_ne_zero a b 0
  exact fun H => hx (congrFun H _)

theorem riemannTheta_unique_eq_tsum [Unique ι] (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω v = ∑' n : ℤ, cexp (π * I * (n + a default) ^ 2 * Ω default default +
      2 * π * I * (n + a default) * (v default + b default)) := by
  rw [riemannTheta_def, ← (Equiv.funUnique ι ℤ).symm.tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [riemannThetaTerm_eq_sum, Fintype.sum_unique, Equiv.funUnique_symm_apply,
    uniqueElim_const]
  congr 1
  ring

theorem riemannTheta_unique_zero_zero [Unique ι] (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta 0 0 Ω v = jacobiTheta₂ (v default) (Ω default default) := by
  rw [riemannTheta_unique_eq_tsum, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  congr 1
  simp only [Pi.zero_apply, ofReal_zero]
  ring

theorem riemannTheta_unique_eq_jacobiTheta₂ [Unique ι] (a b : ι → ℝ) (Ω : Matrix ι ι ℂ)
    (v : ι → ℂ) :
    riemannTheta a b Ω v =
      cexp (π * I * (a default) ^ 2 * Ω default default +
        2 * π * I * a default * (v default + b default)) *
      jacobiTheta₂ (v default + b default + a default * Ω default default) (Ω default default) := by
  rw [riemannTheta_unique_eq_tsum, jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

theorem riemannTheta_fin_one (z τ : ℂ) : riemannTheta 0 0 !![τ] ![z] = jacobiTheta₂ z τ := by
  rw [riemannTheta_unique_zero_zero]
  simp

theorem riemannTheta_submatrix_equiv (e : κ ≃ ι) (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta (a ∘ e) (b ∘ e) (Ω.submatrix e e) (v ∘ e) = riemannTheta a b Ω v := by
  rw [riemannTheta_def, riemannTheta_def, ← (Equiv.arrowCongr e (Equiv.refl ℤ)).symm.tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [riemannThetaTerm_eq_sum, ← e.sum_comp]
  simp

theorem riemannThetaTerm_fromBlocks (a₁ b₁ : ι → ℝ) (a₂ b₂ : κ → ℝ) (Ω₁ : Matrix ι ι ℂ)
    (Ω₂ : Matrix κ κ ℂ) (v₁ : ι → ℂ) (v₂ : κ → ℂ) (n₁ : ι → ℤ) (n₂ : κ → ℤ) :
    riemannThetaTerm (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (fromBlocks Ω₁ 0 0 Ω₂) (Sum.elim v₁ v₂)
        (Sum.elim n₁ n₂) =
      riemannThetaTerm a₁ b₁ Ω₁ v₁ n₁ * riemannThetaTerm a₂ b₂ Ω₂ v₂ n₂ := by
  simp only [riemannThetaTerm_eq_sum, ← Complex.exp_add, Fintype.sum_sum_type]
  congr 1
  simp
  ring

theorem riemannTheta_fromBlocks {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} (h₁ : IsSiegel Ω₁)
    (h₂ : IsSiegel Ω₂) (a₁ b₁ : ι → ℝ) (a₂ b₂ : κ → ℝ) (v₁ : ι → ℂ) (v₂ : κ → ℂ) :
    riemannTheta (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (fromBlocks Ω₁ 0 0 Ω₂) (Sum.elim v₁ v₂) =
      riemannTheta a₁ b₁ Ω₁ v₁ * riemannTheta a₂ b₂ Ω₂ v₂ := by
  rw [riemannTheta_def, riemannTheta_def, riemannTheta_def, tsum_mul_tsum_of_summable_norm
    (h₁.summable_norm_riemannThetaTerm a₁ b₁ v₁) (h₂.summable_norm_riemannThetaTerm a₂ b₂ v₂),
    ← (Equiv.sumArrowEquivProdArrow ι κ ℤ).symm.tsum_eq]
  exact tsum_congr fun n => riemannThetaTerm_fromBlocks ..

theorem riemannTheta_fromBlocks' {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} (h₁ : IsSiegel Ω₁)
    (h₂ : IsSiegel Ω₂) (a b : ι ⊕ κ → ℝ) (v : ι ⊕ κ → ℂ) :
    riemannTheta a b (fromBlocks Ω₁ 0 0 Ω₂) v =
      riemannTheta (a ∘ Sum.inl) (b ∘ Sum.inl) Ω₁ (v ∘ Sum.inl) *
        riemannTheta (a ∘ Sum.inr) (b ∘ Sum.inr) Ω₂ (v ∘ Sum.inr) := by
  rw [← riemannTheta_fromBlocks h₁ h₂]
  simp only [Sum.elim_comp_inl_inr]

section Theta

open ReciprocityTheory.PTheta

theorem summable_norm_thetaTerm_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) :
    Summable fun l => ‖thetaTerm a b z τ l‖ :=
  IsSiegel.summable_norm_riemannThetaTerm h a b z

theorem hasSum_theta_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) :
    HasSum (thetaTerm a b z τ) (theta a b z τ) :=
  IsSiegel.hasSum_riemannTheta h a b z

theorem hasSumLocallyUniformlyOn_theta_siegelH (a b : ι → ℝ) :
    HasSumLocallyUniformlyOn (fun l (p : (ι → ℂ) × Matrix ι ι ℂ) => thetaTerm a b p.1 p.2 l)
      (fun p => theta a b p.1 p.2) (Set.univ ×ˢ SiegelH ι) :=
  hasSumLocallyUniformlyOn_riemannTheta a b

theorem differentiable_theta_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι) (a b : ι → ℝ) :
    Differentiable ℂ fun z => theta a b z τ :=
  IsSiegel.differentiable_riemannTheta h a b

theorem exists_theta_ne_zero_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι) (a b : ι → ℝ) :
    ∃ z, theta a b z τ ≠ 0 :=
  Function.ne_iff.mp (IsSiegel.riemannTheta_ne_zero h a b)

theorem integral_theta_mul_eC_of_mem_siegelH {τ : Matrix ι ι ℂ} (h : τ ∈ SiegelH ι)
    (a b : ι → ℝ) (z : ι → ℂ) (l : ι → ℤ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, theta a b (z + ofRealVec x) τ *
        eC (-(shiftVec a l ⬝ᵥ ofRealVec x)) = thetaTerm a b z τ l := by
  have := IsSiegel.integral_riemannTheta_mul_cexp h a b z l
  simp only [neg_mul] at this
  simp only [eC, mul_neg]
  exact this

theorem riemannTheta_add_eq_autFactor_mul {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b : ι → ℝ)
    (v : ι → ℂ) (k m : ι → ℤ) :
    riemannTheta a b Ω (v + Ω *ᵥ ofIntVec k + ofIntVec m) =
      autFactor a b Ω k m v * riemannTheta a b Ω v := by
  rw [add_assoc, add_comm (Ω *ᵥ _), autFactor, eC, eC, ← Complex.exp_add]
  refine (riemannTheta_add_lattice h a b v m k).trans ?_
  congr 2
  unfold ofRealVec ofIntVec
  ring

theorem theta_fromBlocks_zero {τ₁ : Matrix ι ι ℂ} {τ₂ : Matrix κ κ ℂ} (h₁ : τ₁ ∈ SiegelH ι)
    (h₂ : τ₂ ∈ SiegelH κ) (a₁ b₁ : ι → ℝ) (a₂ b₂ : κ → ℝ) (z₁ : ι → ℂ) (z₂ : κ → ℂ) :
    theta (Sum.elim a₁ a₂) (Sum.elim b₁ b₂) (Sum.elim z₁ z₂) (fromBlocks τ₁ 0 0 τ₂) =
      theta a₁ b₁ z₁ τ₁ * theta a₂ b₂ z₂ τ₂ :=
  riemannTheta_fromBlocks h₁ h₂ a₁ b₁ a₂ b₂ z₁ z₂

end Theta

example : !![1 + 2 * I, 1 / 2 + I; 1 / 2 + I, 2 * I] ∈ ReciprocityTheory.PTheta.SiegelH (Fin 2) :=
  isSiegel_example.mem_siegelH

example (a b : Fin 0 → ℝ) (Ω : Matrix (Fin 0) (Fin 0) ℂ) (v : Fin 0 → ℂ) :
    riemannTheta a b Ω v = 1 := by
  simp [riemannTheta_def, riemannThetaTerm_def, dotProduct]

example : riemannTheta (fun _ => 1 / 2) (fun _ => 1 / 2) !![I] 0 = 0 := by
  have := riemannTheta_half_neg (fun _ : Fin 1 => 1) (fun _ => 1) !![I] 0
  simp only [Int.cast_one, neg_zero, dotProduct, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, one_smul, zpow_one] at this
  linear_combination this / 2

example (b : Fin 1 → ℝ) (z : ℂ) :
    riemannTheta (fun _ => 1 / 2) b !![I] ![z + 1] = -riemannTheta (fun _ => 1 / 2) b !![I] ![z] := by
  have := riemannTheta_add_intCast (fun _ : Fin 1 => 1 / 2) b !![I] ![z] (fun _ => 1)
  have e : (![z] + fun _ => ((1 : ℤ) : ℂ)) = ![z + 1] := by
    funext i
    fin_cases i
    simp
  rw [← e, this]
  have : 2 * π * I * ((fun _ : Fin 1 => ((1 / 2 : ℝ) : ℂ)) ⬝ᵥ fun _ => ((1 : ℤ) : ℂ)) = π * I := by
    simp [dotProduct]
    ring
  rw [this, Complex.exp_pi_mul_I, neg_one_mul]

example (z τ : ℂ) : jacobiTheta₂ (z + τ) τ = cexp (-π * I * (τ + 2 * z)) * jacobiTheta₂ z τ := by
  have hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have := riemannTheta_add_mulVec_intCast hs 0 0 ![z] (fun _ => 1)
  rw [riemannTheta_unique_zero_zero, riemannTheta_fin_one] at this
  convert this using 3
  · simp [mulVec, dotProduct]
  · simp
  · simp [mulVec, dotProduct]
    ring

example : Differentiable ℂ (riemannTheta 0 0 !![1 + 2 * I, 1 / 2 + I; 1 / 2 + I, 2 * I]) ∧
    riemannTheta 0 0 !![1 + 2 * I, 1 / 2 + I; 1 / 2 + I, 2 * I] ≠ 0 :=
  ⟨isSiegel_example.differentiable_riemannTheta 0 0, isSiegel_example.riemannTheta_ne_zero 0 0⟩

end GlobalTheory
