import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamEquivData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

section Bump

def hsOne (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖(g - 1) i j‖ ^ 2

theorem sum_sq_norm_eq_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = (trace (Aᴴ * A)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
    Complex.normSq_apply]
  ring

theorem hsOne_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : hsOne (k * g * star k) = hsOne g := by
  have h1' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have h2 : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have e : k * g * star k - 1 = k * (g - 1) * kᴴ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1']
  have e2 : (k * (g - 1) * kᴴ)ᴴ * (k * (g - 1) * kᴴ) = k * ((g - 1)ᴴ * (g - 1)) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, h2, Matrix.one_mul]
  unfold hsOne
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2,
    Matrix.one_mul]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => g i j) :=
  (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin n → ℂ) i)

theorem contDiff_hsOne : ContDiff ℝ ∞ (hsOne (n := n)) := by
  unfold hsOne
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℂ).comp ((contDiff_entry i j).sub contDiff_const)

def arbB (r : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.smoothTransition (r ^ 2 - hsOne g)

theorem contDiff_arbB (r : ℝ) : ContDiff ℝ ∞ (arbB (n := n) r) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_hsOne)

theorem arbB_nonneg (r : ℝ) (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ arbB r g :=
  Real.smoothTransition.nonneg _

theorem arbB_one_pos {r : ℝ} (hr : 0 < r) : 0 < arbB r (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h0 : hsOne (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hsOne]
  unfold arbB
  rw [h0, sub_zero]
  exact Real.smoothTransition.pos_of_pos (by positivity)

theorem norm_lt_of_arbB_ne {r : ℝ} (hr : 0 < r) {g : Matrix (Fin n) (Fin n) ℂ} (h : arbB r g ≠ 0) :
    ‖g - 1‖ < r := by
  have hlt : hsOne g < r ^ 2 := by
    by_contra hc
    push Not at hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  rw [Matrix.norm_lt_iff hr]
  intro i j
  have h1 : ‖(g - 1) i j‖ ^ 2 ≤ hsOne g := by
    unfold hsOne
    calc ‖(g - 1) i j‖ ^ 2 ≤ ∑ j', ‖(g - 1) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖(g - 1) i j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖(g - 1) i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖(g - 1) i' j'‖ ^ 2) (fun _ _ => by positivity)
            (Finset.mem_univ i)
  have h3 : ‖(g - 1) i j‖ ^ 2 < r ^ 2 := lt_of_le_of_lt h1 hlt
  nlinarith [norm_nonneg ((g - 1) i j)]

theorem hasCompactSupport_arbB {r : ℝ} (hr : 0 < r) : HasCompactSupport (arbB (n := n) r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) fun g hg => ?_
  by_contra h
  exact hg (by rw [Metric.mem_closedBall, dist_eq_norm]; exact (norm_lt_of_arbB_ne hr h).le)

theorem arbB_conj (r : ℝ) {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (g : Matrix (Fin n) (Fin n) ℂ) : arbB r (k * g * star k) = arbB r g := by
  unfold arbB
  rw [hsOne_conj hk.1]

end Bump

section Conv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem arb_umat_cont : Continuous (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.continuous

theorem arb_umat_mem (y : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.umat y ∈ UJset ε := y.2

theorem arb_orbit_cont (hσ : IsURepOn (UJset ε) σ) (w : H) :
    Continuous (fun y : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat y) w) :=
  (hσ.2.2 w).comp_continuous arb_umat_cont arb_umat_mem

theorem arb_rep_mul (hσ : IsURepOn (UJset ε) σ) (a b : Formalism.REAL.UJ ε) (v : H) :
    σ (Formalism.MainNotions.S.umat (a * b)) v = σ (Formalism.MainNotions.S.umat a) (σ (Formalism.MainNotions.S.umat b) v) := by
  show σ (Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b) v = _
  rw [hσ.1.2 _ (arb_umat_mem a) _ (arb_umat_mem b), ContinuousLinearMap.comp_apply]

theorem arb_exists_umat {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ γ : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat γ = g := by
  have : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => ((y : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [(Formalism.REAL.isClosedEmbeddingMatrix n ε).2]; exact hg
  exact this

theorem arb_integrable (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) :
    Integrable (fun y : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) w) (Formalism.REAL.muG ε) :=
  ((hα.comp arb_umat_cont).smul (arb_orbit_cont hσ w)).integrable_of_hasCompactSupport
    ((hαc.comp_isClosedEmbedding (Formalism.REAL.isClosedEmbeddingMatrix n ε).1).smul_right)

theorem opConv_add (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (v w : H) :
    opConv ε σ α (v + w) = opConv ε σ α v + opConv ε σ α w := by
  unfold opConv
  rw [← integral_add (arb_integrable hσ v hα hαc) (arb_integrable hσ w hα hαc)]
  congr 1
  funext y
  rw [map_add, smul_add]

theorem opConv_smul {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (v : H) :
    opConv ε σ α (c • v) = c • opConv ε σ α v := by
  unfold opConv
  rw [← integral_smul]
  congr 1
  funext y
  rw [map_smul, smul_comm]

def opConvL (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) : H →ₗ[ℂ] H where
  toFun := opConv ε σ α
  map_add' := opConv_add hσ hα hαc
  map_smul' := opConv_smul

theorem opConv_comm_K (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} (hα : Continuous α)
    (hαc : HasCompactSupport α) (hαK : IsAdKInv ε α) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (v : H) : σ k (opConv ε σ α v) = opConv ε σ α (σ k v) := by
  have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
  obtain ⟨κ, hκ⟩ := arb_exists_umat hkU
  have hku : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hk.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hku' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hk.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hinv : Formalism.MainNotions.S.umat κ⁻¹ = kᴴ := by
    have h3 : Formalism.MainNotions.S.umat κ⁻¹ * k = 1 := by
      rw [← hκ]
      show Formalism.MainNotions.S.umat (κ⁻¹ * κ) = 1
      rw [inv_mul_cancel]
      rfl
    calc Formalism.MainNotions.S.umat κ⁻¹ = Formalism.MainNotions.S.umat κ⁻¹ * (k * kᴴ) := by rw [hku', Matrix.mul_one]
      _ = kᴴ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  have hF : ∀ y : Formalism.REAL.UJ ε,
      σ k (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) v) =
        (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) (κ * (y * κ⁻¹)) := by
    intro y
    have e1 : Formalism.MainNotions.S.umat (κ * (y * κ⁻¹)) = k * Formalism.MainNotions.S.umat y * star k := by
      show Formalism.MainNotions.S.umat κ * (Formalism.MainNotions.S.umat y * Formalism.MainNotions.S.umat κ⁻¹) = _
      rw [hκ, hinv, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    have m1 : k * Formalism.MainNotions.S.umat y * star k ∈ UJset ε := e1 ▸ arb_umat_mem (κ * (y * κ⁻¹))
    have h4 : k * Formalism.MainNotions.S.umat y * star k * k = k * Formalism.MainNotions.S.umat y := by
      rw [Matrix.mul_assoc (k * _), Matrix.star_eq_conjTranspose, hku, Matrix.mul_one]
    have e2 : σ (k * Formalism.MainNotions.S.umat y * star k) (σ k v) = σ k (σ (Formalism.MainNotions.S.umat y) v) := by
      calc σ (k * Formalism.MainNotions.S.umat y * star k) (σ k v)
          = ((σ (k * Formalism.MainNotions.S.umat y * star k)).comp (σ k)) v := rfl
        _ = σ (k * Formalism.MainNotions.S.umat y * star k * k) v := by rw [hσ.1.2 _ m1 _ hkU]
        _ = σ (k * Formalism.MainNotions.S.umat y) v := by rw [h4]
        _ = σ k (σ (Formalism.MainNotions.S.umat y) v) := by
            rw [hσ.1.2 _ hkU _ (arb_umat_mem y)]
            rfl
    show _ = α (Formalism.MainNotions.S.umat (κ * (y * κ⁻¹))) • σ (Formalism.MainNotions.S.umat (κ * (y * κ⁻¹))) (σ k v)
    rw [e1, hαK k hk, e2, map_smul]
  unfold opConv
  rw [← ContinuousLinearMap.integral_comp_comm _ (arb_integrable hσ v hα hαc)]
  calc ∫ y, σ k (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) v) ∂(Formalism.REAL.muG ε)
      = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v))
          (κ * (y * κ⁻¹)) ∂(Formalism.REAL.muG ε) := by
        congr 1
        funext y
        exact hF y
    _ = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v))
          (κ * y) ∂(Formalism.REAL.muG ε) :=
        integral_mul_right_eq_self
          (fun y => (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) (κ * y)) κ⁻¹
    _ = ∫ y, α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) (σ k v) ∂(Formalism.REAL.muG ε) :=
        integral_mul_left_eq_self
          (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat z) • σ (Formalism.MainNotions.S.umat z) (σ k v)) κ

theorem opConv_translate (hσ : IsURepOn (UJset ε) σ) (w : H) {α : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hα : Continuous α) (hαc : HasCompactSupport α) (γ : Formalism.REAL.UJ ε) :
    σ (Formalism.MainNotions.S.umat γ) (opConv ε σ α w) =
      ∫ y, α (Formalism.MainNotions.S.umat (γ⁻¹ * y)) • σ (Formalism.MainNotions.S.umat y) w ∂(Formalism.REAL.muG ε) := by
  unfold opConv
  rw [← ContinuousLinearMap.integral_comp_comm _ (arb_integrable hσ w hα hαc)]
  calc ∫ y, σ (Formalism.MainNotions.S.umat γ) (α (Formalism.MainNotions.S.umat y) • σ (Formalism.MainNotions.S.umat y) w) ∂(Formalism.REAL.muG ε)
      = ∫ y, (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat (γ⁻¹ * z)) • σ (Formalism.MainNotions.S.umat z) w) (γ * y)
          ∂(Formalism.REAL.muG ε) := by
        congr 1
        funext y
        show _ = α (Formalism.MainNotions.S.umat (γ⁻¹ * (γ * y))) • σ (Formalism.MainNotions.S.umat (γ * y)) w
        rw [inv_mul_cancel_left, map_smul, arb_rep_mul hσ]
    _ = _ := integral_mul_left_eq_self
          (fun z : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat (γ⁻¹ * z)) • σ (Formalism.MainNotions.S.umat z) w) γ

end Conv

end ReciprocityTheory.ChartRestriction.DS
