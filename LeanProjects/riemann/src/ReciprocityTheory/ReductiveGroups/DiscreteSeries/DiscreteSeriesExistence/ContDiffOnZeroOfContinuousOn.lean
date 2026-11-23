import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CayleyChartDomainIsOpen

noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

section Curve

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

local notation "JJ" => Formalism.REAL.Jm

theorem slm_le_inf (N : ℕ) : (N : WithTop ℕ∞) + 1 ≤ ∞ := by
  first
  | exact_mod_cast (le_top : ((N + 1 : ℕ) : ℕ∞) ≤ ⊤)
  | (norm_cast; exact le_top)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp

theorem slm_le_inf' (N : ℕ) : (N : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact_mod_cast (le_top : ((N : ℕ) : ℕ∞) ≤ ⊤)
  | (norm_cast; exact le_top)
  | exact WithTop.coe_le_coe.mpr le_top
  | simp

theorem slm_hd_iff {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} :
    HasDerivAt f f' s ↔ ∀ i j, HasDerivAt (fun t => f t i j) (f' i j) s := by
  first
  | exact hasDerivAt_pi.trans (forall_congr' fun i => hasDerivAt_pi)
  | exact (hasDerivAt_pi (Φ := f)).trans (forall_congr' fun i => hasDerivAt_pi)

theorem slm_hd_mul {f g : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' g' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => f t * g t) (f' * g s + f s * g') s := by
  refine slm_hd_iff.mpr fun i j => ?_
  have hf' := slm_hd_iff.mp hf
  have hg' := slm_hd_iff.mp hg
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  first
  | exact HasDerivAt.fun_sum fun k _ => (hf' i k).mul (hg' k j)
  | exact HasDerivAt.sum fun k _ => (hf' i k).mul (hg' k j)

theorem slm_hd_conjT {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ}
    (hf : HasDerivAt f f' s) : HasDerivAt (fun t => (f t)ᴴ) f'ᴴ s := by
  refine slm_hd_iff.mpr fun i j => ?_
  have h1 := (slm_hd_iff.mp hf j i).star
  simpa [Matrix.conjTranspose_apply] using h1

theorem slm_Ji_mul_mul (a b : Matrix (Fin n) (Fin n) ℂ) : slmJi ε (a * b) = slmJi ε b * slmJi ε a := by
  unfold slmJi
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul]

theorem slm_inG_of_curve {c : ℝ → Matrix (Fin n) (Fin n) ℂ} {c' : Matrix (Fin n) (Fin n) ℂ} {s0 : ℝ}
    (hc : HasDerivAt c c' s0) (hcU : ∀ᶠ s in 𝓝 s0, Formalism.REAL.inUJ ε (c s)) :
    Formalism.REAL.inG ε (slmJi ε (c s0) * c') := by
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hJt := Formalism.REAL.Jm_conjTranspose ε
  have e1 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← mul_assoc, hJ, one_mul]
  have h1 : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε) (c'ᴴ * Formalism.REAL.Jm ε) s0 := by
    have := slm_hd_mul (slm_hd_conjT hc) (hasDerivAt_const s0 (Formalism.REAL.Jm ε))
    simpa using this
  have hD : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε * c s)
      (c'ᴴ * Formalism.REAL.Jm ε * c s0 + (c s0)ᴴ * Formalism.REAL.Jm ε * c') s0 := slm_hd_mul h1 hc
  have hD0 : HasDerivAt (fun s => (c s)ᴴ * Formalism.REAL.Jm ε * c s) 0 s0 := by
    apply (hasDerivAt_const s0 (Formalism.REAL.Jm ε)).congr_of_eventuallyEq
    filter_upwards [hcU] with s hs
    exact hs
  have hsum := hD.unique hD0
  show (slmJi ε (c s0) * c')ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (slmJi ε (c s0) * c') = 0
  unfold slmJi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJt, mul_assoc, hJ,
    Matrix.mul_one, e1]
  simpa [mul_assoc] using hsum

end Curve

section GenG

variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

def slmG (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) : X →L[ℝ] E :=
  ∑ i, ((C i).comp fd).smulRight (w i)

theorem slmG_apply (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) :
    slmG C fd w W = ∑ i, (C i (fd W)) • w i := by
  simp [slmG, ContinuousLinearMap.sum_apply]

theorem slmG_apply' (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) (κ : ι → ℝ)
    (hκ : ∀ i, C i (fd W) = κ i) : slmG C fd w W = ∑ i, κ i • w i := by
  rw [slmG_apply]
  simp only [hκ]

theorem slmG_cd {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {N : ℕ} {w : ι → X → E} (hw : ∀ i, ContDiffOn ℝ N (w i) V) :
    ContDiffOn ℝ N (fun q => slmG C (fderiv ℝ γ q) (fun i => w i q)) V := by
  have hfd : ContDiffOn ℝ N (fun q => fderiv ℝ γ q) V := hγ.fderiv_of_isOpen hV (slm_le_inf N)
  unfold slmG
  first
  | exact ContDiffOn.sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)
  | exact ContDiffOn.fun_sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)
  | simp only [ContinuousLinearMap.sum_apply]
    exact ContDiffOn.sum fun i _ => (contDiffOn_const.clm_comp hfd).smulRight (hw i)

theorem contDiffOn_zero_of_continuousOn {V : Set X} {f : X → E} (h : ContinuousOn f V) : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) f V := by
  first
  | exact contDiffOn_zero.mpr h
  | (rw [Nat.cast_zero]; exact contDiffOn_zero.mpr h)
  | (simp only [Nat.cast_zero, CharP.cast_eq_zero]; exact contDiffOn_zero.mpr h)

theorem slm_gen_hD {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {A : Type*} (c : ι → X → ℂ) (hc : ∀ i, ContDiffOn ℝ ∞ (c i) V)
    (P : A → Prop) (Op : ι → A → A) (hP : ∀ F, P F → ∀ i, P (Op i F)) (Φ : A → X → E)
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : X, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG C (fderiv ℝ γ (q + s • W))
          (fun i => c i (q + s • W) • Φ (Op i F) (q + s • W)) W -
        slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) :
    ∀ F, P F → ∀ q ∈ V,
      HasFDerivAt (Φ F) (slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q)) q := by
  intro F hF q hq
  set L : X → (X →L[ℝ] E) := fun x => slmG C (fderiv ℝ γ x) (fun i => c i x • Φ (Op i F) x)
    with hLdef
  have hw0 : ∀ i, ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun x => c i x • Φ (Op i F) x) V :=
    fun i => contDiffOn_zero_of_continuousOn (((hc i).continuousOn).smul (hcont (Op i F) (hP F hF i)))
  have hLc : ContinuousAt L q :=
    ((slmG_cd hV hγ C hw0).continuousOn).continuousAt (hV.mem_nhds hq)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨ρ, hρ, hρL⟩ := Metric.continuousAt_iff.mp hLc ε hε
  obtain ⟨δ, hδ, hδh⟩ := hint F hF q hq
  have hball : ∀ᶠ W in 𝓝 (0 : X), ‖W‖ < min δ ρ := by
    have := Metric.ball_mem_nhds (0 : X) (lt_min hδ hρ)
    filter_upwards [this] with W hW
    simpa using hW
  filter_upwards [hball] with W hW
  apply hδh W (lt_of_lt_of_le hW (min_le_left _ _)) (ε * ‖W‖)
  intro s hs
  have hd : dist (q + s • W) q < ρ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖W‖ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖W‖ := one_mul _
      _ < ρ := lt_of_lt_of_le hW (min_le_right _ _)
  have h1 := hρL hd
  rw [dist_eq_norm] at h1
  calc ‖L (q + s • W) W - L q W‖ = ‖(L (q + s • W) - L q) W‖ := by
        rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖L (q + s • W) - L q‖ * ‖W‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖W‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)

theorem slm_gen {V : Set X} (hV : IsOpen V) {γ : X → Y} (hγ : ContDiffOn ℝ ∞ γ V)
    (C : ι → Y →L[ℝ] ℝ) {A : Type*} (c : ι → X → ℂ) (hc : ∀ i, ContDiffOn ℝ ∞ (c i) V)
    (P : A → Prop) (Op : ι → A → A) (hP : ∀ F, P F → ∀ i, P (Op i F)) (Φ : A → X → E)
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : X, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG C (fderiv ℝ γ (q + s • W))
          (fun i => c i (q + s • W) • Φ (Op i F) (q + s • W)) W -
        slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG C (fderiv ℝ γ q) (fun i => c i q • Φ (Op i F) q) W‖ ≤ B) :
    ∀ F, P F → ContDiffOn ℝ ∞ (Φ F) V := by
  intro F hF
  have key : ∀ N : ℕ, ∀ F, P F → ContDiffOn ℝ N (Φ F) V := by
    intro N
    induction N with
    | zero => intro F hF; exact contDiffOn_zero_of_continuousOn (hcont F hF)
    | succ N ih =>
      intro F hF
      have hD := slm_gen_hD hV hγ C c hc P Op hP Φ hcont hint F hF
      have hw : ∀ i, ContDiffOn ℝ N (fun q => c i q • Φ (Op i F) q) V := fun i =>
        ((hc i).of_le (slm_le_inf' N)).smul (ih (Op i F) (hP F hF i))
      have hfd : ContDiffOn ℝ N (fderiv ℝ (Φ F)) V :=
        (slmG_cd hV hγ C hw).congr fun q hq => (hD q hq).fderiv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hV]
      exact ⟨fun q hq => (hD q hq).differentiableAt.differentiableWithinAt, by simp, hfd⟩
  exact contDiffOn_infty.mpr fun N => key N F hF

end GenG

section GenM

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def slmEnt (k b : Fin n) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) k)

theorem slmEnt_apply (k b : Fin n) (W : Fin n → Fin n → ℂ) : slmEnt k b W = W k b := rfl

def slmC (i : Fin n × Fin n × Fin n × Bool) :=
  if i.2.2.2 then Complex.reCLM.comp (slmEnt i.2.2.1 i.2.1) else Complex.imCLM.comp (slmEnt i.2.2.1 i.2.1)

def slmc (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (i : Fin n × Fin n × Fin n × Bool)
    (q : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if i.2.2.2 then m q i.1 i.2.2.1 else Complex.I * m q i.1 i.2.2.1

theorem re_mul_add_im_mul_I (z c : ℂ) : (z.re : ℂ) * c + (z.im : ℂ) * (Complex.I * c) = c * z := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring

theorem slmc_cd {V : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hm : ContDiffOn ℝ ∞ m V) (i : Fin n × Fin n × Fin n × Bool) : ContDiffOn ℝ ∞ (slmc m i) V := by
  have h1 : ContDiffOn ℝ ∞ (fun q => m q i.1 i.2.2.1) V :=
    (slmEnt i.1 i.2.2.1).contDiff.comp_contDiffOn hm
  unfold slmc
  split_ifs
  · exact h1
  · exact contDiffOn_const.mul h1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem slmG_mat_apply (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (q : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → Fin n → E) (W : Matrix (Fin n) (Fin n) ℂ) :
    slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • v i.1 i.2.1) W =
      ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • v a b := by
  refine (slmG_apply (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) _ W).trans ?_
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slmC, slmc, ↓reduceIte, Bool.false_eq_true,
    ContinuousLinearMap.coe_comp', Function.comp_apply, slmEnt_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Matrix.mul_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => ?_
  rw [← re_mul_add_im_mul_I (fderiv ℝ γ q W k b) (m q a k)]
  simp only [add_smul, mul_smul, Complex.coe_smul]
  rfl

theorem slm_mat_hint {V : Set (Matrix (Fin n) (Fin n) ℂ)}
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) :
    ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ (q + s • W))
          (fun i => slmc m i (q + s • W) • Φ (Op i.1 i.2.1 F) (q + s • W)) W -
        slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q) (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q) W‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q)
        (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q) W‖ ≤ B := by
  intro F hF q hq
  obtain ⟨δ, hδ, h⟩ := hint F hF q hq
  refine ⟨δ, hδ, fun W hW B hB => ?_⟩
  rw [slmG_mat_apply γ m q (fun a b => Φ (Op a b F) q) W]
  refine h W hW B fun s hs => ?_
  have h1 := hB s hs
  rwa [slmG_mat_apply γ m (q + s • W) (fun a b => Φ (Op a b F) (q + s • W)) W,
    slmG_mat_apply γ m q (fun a b => Φ (Op a b F) q) W] at h1

theorem slm_mat_hD {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hm : ContDiffOn ℝ ∞ m V) (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hP : ∀ F, P F → ∀ a b, P (Op a b F))
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (hF : P F) (q : Matrix (Fin n) (Fin n) ℂ) (hq : q ∈ V) :
    HasFDerivAt (Φ F) (slmG (Y := Matrix (Fin n) (Fin n) ℂ) slmC (fderiv ℝ γ q)
      (fun i => slmc m i q • Φ (Op i.1 i.2.1 F) q)) q :=
  slm_gen_hD hV hγ slmC (fun i => slmc m i) (fun i => slmc_cd hm i) P (fun i => Op i.1 i.2.1)
    (fun F hF i => hP F hF i.1 i.2.1) Φ hcont (slm_mat_hint Φ P Op hint) F hF q hq

theorem slm_mat {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hm : ContDiffOn ℝ ∞ m V) (Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → E)
    (P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop)
    (Op : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hP : ∀ F, P F → ∀ a b, P (Op a b F))
    (hcont : ∀ F, P F → ContinuousOn (Φ F) V)
    (hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((m (q + s • W) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Op a b F) (q + s • W)) - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((m q * fderiv ℝ γ q W) a b) • Φ (Op a b F) q‖ ≤ B) :
    ∀ F, P F → ContDiffOn ℝ ∞ (Φ F) V :=
  slm_gen hV hγ slmC (fun i => slmc m i) (fun i => slmc_cd hm i) P (fun i => Op i.1 i.2.1)
    (fun F hF i => hP F hF i.1 i.2.1) Φ hcont (slm_mat_hint Φ P Op hint)

end GenM

section Lp

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem slm_coeFn_sum {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    (⇑(∑ i ∈ s, f i) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  · intro i t hi ih
    rw [Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans ?_
    filter_upwards [ih] with x hx
    simp only [Pi.add_apply, hx, Finset.sum_insert hi]

end Lp

end ReciprocityTheory.ChartRestriction.DS
