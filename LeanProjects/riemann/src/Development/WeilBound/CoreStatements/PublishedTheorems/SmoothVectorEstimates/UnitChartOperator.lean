import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace UnitChartOperator

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

def mulI (M N : LieI ι a) : LieI ι a := Matrix.of.symm (Matrix.of M * Matrix.of N)

def gI (g : GL (Fin a) (ι → ℂ)) : LieI ι a := Matrix.of.symm g.val

theorem mulI_gI (g h : GL (Fin a) (ι → ℂ)) : mulI (gI g) (gI h) = gI (g * h) := by
  simp [mulI, gI]

theorem gI_one : gI (1 : GL (Fin a) (ι → ℂ)) = oneI ι a := rfl

theorem mulI_assoc (M N P : LieI ι a) : mulI (mulI M N) P = mulI M (mulI N P) := by
  simp [mulI, Matrix.mul_assoc]

theorem oneI_mulI (M : LieI ι a) : mulI (oneI ι a) M = M := by simp [mulI, oneI]

def lmul (M : LieI ι a) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap
    { toFun := mulI M
      map_add' := fun N P => by simp only [mulI, ← Matrix.of_add_of, Matrix.mul_add]; rfl
      map_smul' := fun c N => by
        ext i k t
        simp [mulI, Matrix.mul_apply, Finset.mul_sum, mul_left_comm] }

def rmul (M : LieI ι a) : LieI ι a →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => mulI N M
      map_add' := fun N P => by simp only [mulI, ← Matrix.of_add_of, Matrix.add_mul]; rfl
      map_smul' := fun c N => by
        ext i k t
        simp [mulI, Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

@[simp] theorem lmul_apply (M N : LieI ι a) : lmul M N = mulI M N := rfl

@[simp] theorem rmul_apply (M N : LieI ι a) : rmul M N = mulI N M := rfl

end Chart

section Orb

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X))

theorem orb_zero : orb ρ (0 : X) = 0 := by
  funext M; simp [orb]

theorem orb_add (v w : X) : orb ρ (v + w) = orb ρ v + orb ρ w := by
  funext M; by_cases h : IsUnit (Matrix.of M) <;> simp [orb, h]

theorem orb_smul (c : ℂ) (v : X) : orb ρ (c • v) = c • orb ρ v := by
  funext M; by_cases h : IsUnit (Matrix.of M) <;> simp [orb, h]

end Orb

section Rap

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def Rap {E : Type} [NormedAddCommGroup E] (f : V → E) : Prop :=
  Continuous f ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖f y‖ ≤ C

def PolyG (m : V → ℂ) : Prop := Continuous m ∧ ∃ (C : ℝ) (k : ℕ), ∀ y, ‖m y‖ ≤ C * (1 + ‖y‖) ^ k

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)}

theorem gI_u {u : V → GL (Fin a) (ι → ℂ)} {L : V →L[ℝ] LieI ι a} (hu : ∀ y, (u y).val = 1 + Matrix.of (L y))
    (y : V) : gI (u y) = oneI ι a + L y := by
  simp only [gI, hu, oneI]; rfl

theorem gI_u_inv {u : V → GL (Fin a) (ι → ℂ)} {L : V →L[ℝ] LieI ι a}
    (hu' : ∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y)) (y : V) : gI (u y)⁻¹ = oneI ι a - L y := by
  simp only [gI, hu', oneI]; rfl

def Mult (𝒢 : Submodule ℂ (V → X)) : Submodule ℂ (V → X) :=
  Submodule.span ℂ {H | ∃ G ∈ 𝒢, ∃ m, PolyG m ∧ H = fun y => m y • G y}

end Rap

section Fca

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

theorem exists_mulI_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ M N : LieI ι a, ‖mulI M N‖ ≤ K * ‖M‖ * ‖N‖ := by
  refine ⟨a, Nat.cast_nonneg _, fun M N => ?_⟩
  have hMN : 0 ≤ (a : ℝ) * ‖M‖ * ‖N‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hMN).2 fun i => (pi_norm_le_iff_of_nonneg hMN).2 fun k => ?_
  have e : mulI M N i k = ∑ j, M i j * N j k := by simp [mulI, Matrix.mul_apply]
  rw [e]
  calc ‖∑ j, M i j * N j k‖ ≤ ∑ j : Fin a, ‖M i j‖ * ‖N j k‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_mul_le _ _)
    _ ≤ ∑ _j : Fin a, ‖M‖ * ‖N‖ := Finset.sum_le_sum fun j _ =>
        mul_le_mul ((norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i))
          ((norm_le_pi_norm (N j) k).trans (norm_le_pi_norm N j)) (norm_nonneg _) (norm_nonneg _)
    _ = a * ‖M‖ * ‖N‖ := by simp [mul_assoc]

section Op

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing

theorem a_hsgs : HasSummableGeomSeries (Matrix (Fin a) (Fin a) (ι → ℂ)) := by
  letI : NormedSpace ℝ (Matrix (Fin a) (Fin a) (ι → ℂ)) := Matrix.linftyOpNormedSpace
  have : FiniteDimensional ℝ (Matrix (Fin a) (Fin a) (ι → ℂ)) := by infer_instance
  have := FiniteDimensional.complete ℝ (Matrix (Fin a) (Fin a) (ι → ℂ))
  infer_instance

theorem a_sup_le_op (A : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    ‖(Matrix.of.symm A : LieI ι a)‖ ≤ ‖A‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
  show ‖A i k‖ ≤ ‖A‖
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖A i k‖₊ ≤ ∑ j, ‖A i j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ k)
  have h2 : ∑ j, ‖A i j‖₊ ≤ Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  exact_mod_cast h1.trans h2

theorem a_op_le_sup (A : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    ‖A‖ ≤ a * ‖(Matrix.of.symm A : LieI ι a)‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (a : NNReal) * ‖(Matrix.of.symm A : LieI ι a)‖₊ := by
    refine Finset.sup_le fun i _ => ?_
    calc ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin a, ‖(Matrix.of.symm A : LieI ι a)‖₊ :=
          Finset.sum_le_sum fun j _ =>
            (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm (Matrix.of.symm A : LieI ι a) i)
      _ = a * ‖(Matrix.of.symm A : LieI ι a)‖₊ := by simp
  exact_mod_cast this

theorem exists_inv_bound : ∃ ε > (0 : ℝ), ∃ B : ℝ, ∀ M ∈ Metric.ball (oneI ι a) ε,
    ∃ g : GL (Fin a) (ι → ℂ), gI g = M ∧ ‖gI g⁻¹‖ ≤ B := by
  refine ⟨1 / (2 * (a + 1)), by positivity, ‖(1 : Matrix (Fin a) (Fin a) (ι → ℂ))‖ - 1 + 2, fun M hM => ?_⟩
  have := a_hsgs (ι := ι) (a := a)
  set T : Matrix (Fin a) (Fin a) (ι → ℂ) := 1 - Matrix.of M with hT
  have hTs : (Matrix.of.symm T : LieI ι a) = oneI ι a - M := rfl
  have hd : ‖oneI ι a - M‖ < 1 / (2 * (a + 1)) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hM; exact hM
  have hT1 : ‖T‖ ≤ 1 / 2 := by
    have h := a_op_le_sup T
    rw [hTs] at h
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have : (a : ℝ) * ‖oneI ι a - M‖ ≤ a * (1 / (2 * (a + 1))) :=
      mul_le_mul_of_nonneg_left hd.le ha
    have h3 : (a : ℝ) * (1 / (2 * (a + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hTlt : ‖T‖ < 1 := by linarith
  refine ⟨Units.oneSub T hTlt, ?_, ?_⟩
  · show Matrix.of.symm (1 - T) = M
    rw [hT, sub_sub_cancel]; rfl
  · refine (a_sup_le_op _).trans ?_
    show ‖∑' n : ℕ, T ^ n‖ ≤ _
    refine (tsum_geometric_le_of_norm_lt_one T hTlt).trans ?_
    have : (1 - ‖T‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith

end Op

end Chart

end Fca

section Fb

section Orb

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X))

theorem orb_gI (g : GL (Fin a) (ι → ℂ)) (v : X) : orb ρ v (gI g) = ρ g v := by
  have h : IsUnit (Matrix.of (gI g)) := by simpa [gI] using g.isUnit
  have hu : h.unit = g := Units.ext (by simp [gI])
  simp only [orb]
  rw [dif_pos h, hu]

theorem orb_mulI (g : GL (Fin a) (ι → ℂ)) (v : X) (M : LieI ι a) :
    orb ρ v (mulI (gI g) M) = ρ g (orb ρ v M) := by
  have e : Matrix.of (mulI (gI g) M) = (g : Matrix (Fin a) (Fin a) (ι → ℂ)) * Matrix.of M := by
    simp [mulI, gI]
  by_cases h : IsUnit (Matrix.of M)
  · have h' : IsUnit (Matrix.of (mulI (gI g) M)) := by rw [e]; exact g.isUnit.mul h
    have hu : h'.unit = g * h.unit := Units.ext (by simp [e])
    simp only [orb]
    rw [dif_pos h', dif_pos h, hu, map_mul, ContinuousLinearMap.mul_apply]
  · have h' : ¬ IsUnit (Matrix.of (mulI (gI g) M)) := by rw [e, Units.isUnit_units_mul]; exact h
    simp only [orb]
    rw [dif_neg h', dif_neg h, map_zero]

theorem orb_mulI_right (g : GL (Fin a) (ι → ℂ)) (v : X) (M : LieI ι a) :
    orb ρ v (mulI M (gI g)) = orb ρ (ρ g v) M := by
  have e : Matrix.of (mulI M (gI g)) = Matrix.of M * (g : Matrix (Fin a) (Fin a) (ι → ℂ)) := by
    simp [mulI, gI]
  by_cases h : IsUnit (Matrix.of M)
  · have h' : IsUnit (Matrix.of (mulI M (gI g))) := by rw [e]; exact h.mul g.isUnit
    have hu : h'.unit = h.unit * g := Units.ext (by simp [e])
    simp only [orb]
    rw [dif_pos h', dif_pos h, hu, map_mul, ContinuousLinearMap.mul_apply]
  · have h' : ¬ IsUnit (Matrix.of (mulI M (gI g))) := by rw [e, Units.isUnit_mul_units]; exact h
    simp only [orb]
    rw [dif_neg h', dif_neg h]

theorem hasFDerivAt_orb_at {v : X} {D : LieI ι a →L[ℝ] X} (hD : HasFDerivAt (orb ρ v) D (oneI ι a))
    (g : GL (Fin a) (ι → ℂ)) :
    HasFDerivAt (orb ρ v) (((ρ g).restrictScalars ℝ).comp (D.comp (lmul (gI g⁻¹)))) (gI g) := by
  have e : orb ρ v = fun N => ((ρ g).restrictScalars ℝ) (orb ρ v (lmul (gI g⁻¹) N)) := by
    funext N
    simp only [ContinuousLinearMap.coe_restrictScalars', lmul_apply]
    rw [← orb_mulI, ← mulI_assoc, mulI_gI, mul_inv_cancel, gI_one, oneI_mulI]
  have h1 : lmul (gI g⁻¹) (gI g) = oneI ι a := by
    rw [lmul_apply, mulI_gI, inv_mul_cancel, gI_one]
  have hD' : HasFDerivAt (orb ρ v) D (lmul (gI g⁻¹) (gI g)) := h1 ▸ hD
  have := ((ρ g).restrictScalars ℝ).hasFDerivAt.comp (gI g) (hD'.comp (gI g) (lmul (gI g⁻¹)).hasFDerivAt)
  rw [e]
  exact this

theorem polyBd_opNorm (hρ : PolyBd ρ) : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
    ∀ g : GL (Fin a) (ι → ℂ), ‖ρ g‖ ≤ C * (1 + ‖gI g‖ + ‖gI g⁻¹‖) ^ N := by
  obtain ⟨C, N, hC, h⟩ := hρ
  exact ⟨C, N, hC, fun g => ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC (pow_nonneg (by positivity) _)) (fun x => h g x)⟩

end Orb

end Fb

section Fc

open Filter

section RapC

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem c_decay {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : V → E} {g : V → F}
    (hg : ∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖g y‖ ≤ C) (K : ℝ) (k : ℕ)
    (hle : ∀ y, ‖f y‖ ≤ K * (1 + ‖y‖) ^ k * ‖g y‖) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ y, (1 + ‖y‖) ^ N * ‖f y‖ ≤ C := by
  intro N
  obtain ⟨C, hC⟩ := hg (N + k)
  refine ⟨max K 0 * C, fun y => ?_⟩
  have h0 : 0 ≤ (1 + ‖y‖) ^ N := by positivity
  have h1 : 0 ≤ (1 + ‖y‖) ^ k * ‖g y‖ := by positivity
  have h2 : ‖f y‖ ≤ max K 0 * ((1 + ‖y‖) ^ k * ‖g y‖) := by
    rw [← mul_assoc]
    exact (hle y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (norm_nonneg _))
  calc (1 + ‖y‖) ^ N * ‖f y‖ ≤ (1 + ‖y‖) ^ N * (max K 0 * ((1 + ‖y‖) ^ k * ‖g y‖)) :=
        mul_le_mul_of_nonneg_left h2 h0
    _ = max K 0 * ((1 + ‖y‖) ^ (N + k) * ‖g y‖) := by rw [pow_add]; ring
    _ ≤ max K 0 * C := mul_le_mul_of_nonneg_left (hC y) (le_max_right _ _)

theorem integrable_of_rap [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {E : Type} [NormedAddCommGroup E] {f : V → E} (hf : Rap f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.2 (Module.finrank ℝ V + 1)
  have hi : Integrable (fun y : V => (1 + ‖y‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ))) μ :=
    integrable_one_add_norm (by push_cast; linarith)
  refine (hi.const_mul C).mono' hf.1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hpos : 0 < (1 + ‖y‖) ^ (Module.finrank ℝ V + 1) := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hC y

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)}

theorem rap_rho (hρ : PolyBd ρ) {u : V → GL (Fin a) (ι → ℂ)} {L : V →L[ℝ] LieI ι a}
    (hu : ∀ y, (u y).val = 1 + Matrix.of (L y)) (hu' : ∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y))
    {H : V → X} (hH : Rap H) (hd : ∀ y, ∃ D : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ (H y)) D (oneI ι a)) :
    Rap (fun y => ρ (u y) (H y)) := by
  obtain ⟨C, N, hC0, hC⟩ := polyBd_opNorm ρ hρ
  set A : ℝ := ‖oneI ι a‖ + ‖L‖ + 1 with hAdef
  have hbd : ∀ y, ‖ρ (u y)‖ ≤ C * (2 * A * (1 + ‖y‖)) ^ N := by
    intro y
    refine (hC (u y)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) hC0)
    rw [gI_u hu, gI_u_inv hu']
    have h1 := norm_add_le (oneI ι a) (L y)
    have h2 := norm_sub_le (oneI ι a) (L y)
    have h3 := L.le_opNorm y
    have h4 : 0 ≤ ‖y‖ := norm_nonneg _
    have h5 : 0 ≤ ‖L‖ := norm_nonneg _
    have h6 : 0 ≤ ‖oneI ι a‖ := norm_nonneg _
    rw [hAdef]
    nlinarith [mul_nonneg h6 h4]
  have hdec := c_decay hH.2 (C * (2 * A) ^ N) N fun y => by
    calc ‖ρ (u y) (H y)‖ ≤ ‖ρ (u y)‖ * ‖H y‖ := (ρ (u y)).le_opNorm _
      _ ≤ C * (2 * A * (1 + ‖y‖)) ^ N * ‖H y‖ := mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _)
      _ = C * (2 * A) ^ N * (1 + ‖y‖) ^ N * ‖H y‖ := by rw [mul_pow]; ring
  refine ⟨continuous_iff_continuousAt.2 fun y0 => ?_, hdec⟩
  obtain ⟨D, hD⟩ := hd y0
  have hcu : Continuous fun y => gI (u y) := by
    simp_rw [gI_u hu]; exact continuous_const.add L.continuous
  have h2 : ContinuousAt (fun y => ρ (u y) (H y0)) y0 := by
    have := (hasFDerivAt_orb_at ρ hD (u y0)).continuousAt.comp (f := fun y => gI (u y)) hcu.continuousAt
    simpa [Function.comp_def, orb_gI] using this
  have hP : Continuous fun y : V => C * (2 * A * (1 + ‖y‖)) ^ N := by fun_prop
  have h1 : Tendsto (fun y => ρ (u y) (H y - H y0)) (𝓝 y0) (𝓝 0) := by
    have ht : Tendsto (fun y => C * (2 * A * (1 + ‖y‖)) ^ N * ‖H y - H y0‖) (𝓝 y0)
        (𝓝 (C * (2 * A * (1 + ‖y0‖)) ^ N * 0)) := by
      refine (hP.tendsto y0).mul ?_
      have := ((hH.1.tendsto y0).sub_const (H y0)).norm
      simpa using this
    rw [mul_zero] at ht
    refine squeeze_zero_norm (fun y => ?_) ht
    exact ((ρ (u y)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbd y) (norm_nonneg _))
  have e : (fun y => ρ (u y) (H y)) = fun y => ρ (u y) (H y - H y0) + ρ (u y) (H y0) := by
    funext y; rw [← map_add, sub_add_cancel]
  rw [e]
  unfold ContinuousAt
  have := h1.add h2
  simpa using this

end RapC

end Fc

section Fd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)}

theorem d_polyG_one : PolyG (fun _ : V => (1 : ℂ)) :=
  ⟨continuous_const, 1, 0, fun y => by simp⟩

theorem d_polyG_mul {m m' : V → ℂ} (hm : PolyG m) (hm' : PolyG m') : PolyG (fun y => m y * m' y) := by
  obtain ⟨hc, C, k, hC⟩ := hm
  obtain ⟨hc', C', k', hC'⟩ := hm'
  refine ⟨hc.mul hc', C * C', k + k', fun y => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖m y‖ * ‖m' y‖ ≤ (C * (1 + ‖y‖) ^ k) * (C' * (1 + ‖y‖) ^ k') :=
        mul_le_mul (hC y) (hC' y) (norm_nonneg _) (le_trans (norm_nonneg _) (hC y))
    _ = C * C' * ((1 + ‖y‖) ^ k * (1 + ‖y‖) ^ k') := by ring

theorem mem_mult {𝒢 : Submodule ℂ (V → X)} {G : V → X} (hG : G ∈ 𝒢) : G ∈ Mult 𝒢 := by
  refine Submodule.subset_span ⟨G, hG, fun _ => 1, d_polyG_one, ?_⟩
  funext y; simp

theorem mult_mul {𝒢 : Submodule ℂ (V → X)} {H : V → X} (hH : H ∈ Mult 𝒢) {m : V → ℂ} (hm : PolyG m) :
    (fun y => m y • H y) ∈ Mult 𝒢 := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, m0, hm0, rfl⟩ := hx
    refine Submodule.subset_span ⟨G, hG, fun y => m y * m0 y, d_polyG_mul hm hm0, ?_⟩
    funext y; simp [mul_smul]
  | zero =>
    convert Submodule.zero_mem (Mult 𝒢) using 1
    funext y; simp
  | add x z _ _ hx hz =>
    convert Submodule.add_mem _ hx hz using 1
    funext y; simp [smul_add]
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    funext y; simp [smul_comm (m y) c]

theorem rapidFam_mult {𝒢 : Submodule ℂ (V → X)} (h𝒢 : RapidFam ρ 𝒢) : RapidFam ρ (Mult 𝒢) := by
  intro H hH
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨G, hG, m, ⟨hmc, C, k, hC⟩, rfl⟩ := hx
    obtain ⟨hGc, hGr, D, hD𝒢, hD⟩ := h𝒢 G hG
    refine ⟨hmc.smul hGc, fun N => ?_, fun Z y => m y • D Z y, fun Z => ?_, fun y => ?_⟩
    · obtain ⟨C', hC'⟩ := hGr (N + k)
      refine ⟨max C 0 * C', fun y => ?_⟩
      have hmy : ‖m y‖ ≤ max C 0 * (1 + ‖y‖) ^ k :=
        (hC y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      rw [norm_smul]
      calc (1 + ‖y‖) ^ N * (‖m y‖ * ‖G y‖)
          ≤ (1 + ‖y‖) ^ N * ((max C 0 * (1 + ‖y‖) ^ k) * ‖G y‖) := by gcongr
        _ = max C 0 * ((1 + ‖y‖) ^ (N + k) * ‖G y‖) := by rw [pow_add]; ring
        _ ≤ max C 0 * C' := mul_le_mul_of_nonneg_left (hC' y) (le_max_right _ _)
    · exact Submodule.subset_span ⟨D Z, hD𝒢 Z, m, ⟨hmc, C, k, hC⟩, rfl⟩
    · obtain ⟨D', hD'1, hD'2⟩ := hD y
      refine ⟨m y • D', fun Z => by simp [hD'1], ?_⟩
      show HasFDerivAt (orb ρ (m y • G y)) _ _
      rw [orb_smul]
      exact hD'2.const_smul (m y)
  | zero =>
    refine ⟨continuous_zero, fun N => ⟨0, fun y => by simp⟩, fun _ => 0, fun _ => Submodule.zero_mem _,
      fun y => ⟨0, fun Z => by simp, ?_⟩⟩
    show HasFDerivAt (orb ρ 0) _ _
    rw [orb_zero]
    exact hasFDerivAt_const _ _
  | add x z _ _ hx hz =>
    obtain ⟨hxc, hxr, Dx, hDx, hx'⟩ := hx
    obtain ⟨hzc, hzr, Dz, hDz, hz'⟩ := hz
    refine ⟨hxc.add hzc, fun N => ?_, fun Z => Dx Z + Dz Z, fun Z => Submodule.add_mem _ (hDx Z) (hDz Z),
      fun y => ?_⟩
    · obtain ⟨C1, h1⟩ := hxr N
      obtain ⟨C2, h2⟩ := hzr N
      refine ⟨C1 + C2, fun y => ?_⟩
      have e1 := h1 y
      have e2 := h2 y
      calc (1 + ‖y‖) ^ N * ‖(x + z) y‖ ≤ (1 + ‖y‖) ^ N * (‖x y‖ + ‖z y‖) := by
            gcongr; exact norm_add_le (x y) (z y)
        _ ≤ C1 + C2 := by rw [mul_add]; linarith
    · obtain ⟨D1, e1, h1⟩ := hx' y
      obtain ⟨D2, e2, h2⟩ := hz' y
      refine ⟨D1 + D2, fun Z => by simp [e1, e2], ?_⟩
      show HasFDerivAt (orb ρ (x y + z y)) _ _
      rw [orb_add]
      exact h1.add h2
  | smul c x _ hx =>
    obtain ⟨hxc, hxr, Dx, hDx, hx'⟩ := hx
    refine ⟨hxc.const_smul c, fun N => ?_, fun Z => c • Dx Z, fun Z => Submodule.smul_mem _ c (hDx Z),
      fun y => ?_⟩
    · obtain ⟨C1, h1⟩ := hxr N
      refine ⟨‖c‖ * C1, fun y => ?_⟩
      calc (1 + ‖y‖) ^ N * ‖(c • x) y‖ = ‖c‖ * ((1 + ‖y‖) ^ N * ‖x y‖) := by
            rw [Pi.smul_apply, norm_smul]; ring
        _ ≤ ‖c‖ * C1 := mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)
    · obtain ⟨D1, e1, h1⟩ := hx' y
      refine ⟨c • D1, fun Z => by simp [e1], ?_⟩
      show HasFDerivAt (orb ρ (c • x y)) _ _
      rw [orb_smul]
      exact h1.const_smul c

end Fd

section Fe

section KeyE

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

open Classical in

def unitChartOperator (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (M : LieI ι a) : X →L[ℂ] X :=
  if h : IsUnit (Matrix.of M) then ρ h.unit else 0

theorem e_orb_eq (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (w : X) (M : LieI ι a) :
    orb ρ w M = unitChartOperator ρ M w := by
  unfold orb unitChartOperator; split_ifs <;> simp

theorem e_isUnit_gI (g : GL (Fin a) (ι → ℂ)) : IsUnit (Matrix.of (gI g)) := by
  have : Matrix.of (gI g) = g.val := rfl
  rw [this]; exact g.isUnit

theorem e_unit_gI (g : GL (Fin a) (ι → ℂ)) (h : IsUnit (Matrix.of (gI g))) : h.unit = g := by
  ext1; rfl

def e_b (ι : Type) [Fintype ι] (a : ℕ) := Module.finBasis ℝ (LieI ι a)

def e_crd (i : Fin (Module.finrank ℝ (LieI ι a))) : LieI ι a →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((e_b ι a).coord i)

@[simp] theorem e_crd_apply (i : Fin (Module.finrank ℝ (LieI ι a))) (Z : LieI ι a) :
    e_crd i Z = (e_b ι a).coord i Z := rfl

variable {V : Type}

def e_Dy (D : LieI ι a → V → X) (y : V) : LieI ι a →L[ℝ] X :=
  ∑ i, (e_crd i).smulRight (D (e_b ι a i) y)

theorem e_Dy_apply (D : LieI ι a → V → X) (y : V) (W : LieI ι a) :
    e_Dy D y W = ∑ i, ((e_b ι a).coord i W : ℂ) • D (e_b ι a i) y := by
  simp [e_Dy, Complex.coe_smul]

theorem e_Dy_eq (D : LieI ι a → V → X) (y : V) (D' : LieI ι a →L[ℝ] X) (h : ∀ Z, D' Z = D Z y) :
    D' = e_Dy D y := by
  ext Z
  rw [e_Dy_apply]
  conv_lhs => rw [← (e_b ι a).sum_repr Z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, h]
  simp [Complex.coe_smul]

theorem e_Dy_norm (D : LieI ι a → V → X) (y : V) :
    ‖e_Dy D y‖ ≤ ∑ i, ‖e_crd (ι := ι) (a := a) i‖ * ‖D (e_b ι a i) y‖ := by
  unfold e_Dy
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [ContinuousLinearMap.norm_smulRight_apply]

theorem e_mulI_cont : Continuous (fun p : LieI ι a × LieI ι a => mulI p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun k => continuous_pi fun t => ?_
  simp only [mulI, Matrix.of_symm_apply, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
  fun_prop

theorem e_mulI_cont' {Y : Type} [TopologicalSpace Y] {f g : Y → LieI ι a} (hf : Continuous f)
    (hg : Continuous g) : Continuous (fun y => mulI (f y) (g y)) :=
  e_mulI_cont.comp (hf.prodMk hg)

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem e_rap_weight {E : Type} [NormedAddCommGroup E] {f : V → E} (hf : Rap f) (k : ℕ) :
    Rap (fun y => (1 + ‖y‖) ^ k * ‖f y‖) := by
  refine ⟨((continuous_const.add continuous_norm).pow k).mul hf.1.norm, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hf.2 (N + k)
  refine ⟨C, fun y => ?_⟩
  have h0 : 0 ≤ 1 + ‖y‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc, ← pow_add]
  exact hC y

end KeyE

section KeyMain

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem e_lmul_norm {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ M N : LieI ι a, ‖mulI M N‖ ≤ K * ‖M‖ * ‖N‖)
    (P : LieI ι a) : ‖lmul P‖ ≤ K * ‖P‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun N => by simpa using hK P N

theorem e_rmul_norm {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ M N : LieI ι a, ‖mulI M N‖ ≤ K * ‖M‖ * ‖N‖)
    (P : LieI ι a) : ‖rmul P‖ ≤ K * ‖P‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun N => by
    have := hK N P; simp only [rmul_apply]; nlinarith [norm_nonneg N, norm_nonneg P]

theorem e_gI_u_norm {u : V → GL (Fin a) (ι → ℂ)} {L : V →L[ℝ] LieI ι a}
    (hu : ∀ y, (u y).val = 1 + Matrix.of (L y)) (hu' : ∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y)) (y : V) :
    ‖gI (u y)‖ ≤ (‖oneI ι a‖ + ‖L‖) * (1 + ‖y‖) ∧ ‖gI (u y)⁻¹‖ ≤ (‖oneI ι a‖ + ‖L‖) * (1 + ‖y‖) := by
  have h1 := L.le_opNorm y
  have h2 : ‖oneI ι a‖ + ‖L‖ * ‖y‖ ≤ (‖oneI ι a‖ + ‖L‖) * (1 + ‖y‖) := by
    nlinarith [norm_nonneg (oneI ι a), norm_nonneg L, norm_nonneg y]
  refine ⟨?_, ?_⟩
  · rw [gI_u hu]; exact (norm_add_le _ _).trans (by linarith)
  · rw [gI_u_inv hu']; exact (norm_sub_le _ _).trans (by linarith)

theorem e_polyG_coord {u : V → GL (Fin a) (ι → ℂ)} {L : V →L[ℝ] LieI ι a}
    (hu : ∀ y, (u y).val = 1 + Matrix.of (L y)) (hu' : ∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y))
    (Z : LieI ι a) (i : Fin (Module.finrank ℝ (LieI ι a))) :
    PolyG (fun y => (((e_b ι a).coord i (mulI (gI (u y)⁻¹) (mulI Z (gI (u y)))) : ℝ) : ℂ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_mulI_bound (ι := ι) (a := a)
  refine ⟨?_, ?_⟩
  · have hc : Continuous fun y => mulI (gI (u y)⁻¹) (mulI Z (gI (u y))) := by
      simp only [gI_u hu, gI_u_inv hu']
      have hP : Continuous fun y => oneI ι a - L y := continuous_const.sub L.continuous
      have hQ : Continuous fun y => oneI ι a + L y := continuous_const.add L.continuous
      exact e_mulI_cont' hP (e_mulI_cont' continuous_const hQ)
    have h2 : Continuous fun y => e_crd (ι := ι) (a := a) i (mulI (gI (u y)⁻¹) (mulI Z (gI (u y)))) :=
      (e_crd (ι := ι) (a := a) i).continuous.comp hc
    simp only [e_crd_apply] at h2
    exact Complex.continuous_ofReal.comp h2
  · refine ⟨‖e_crd (ι := ι) (a := a) i‖ * (K * (K * ‖Z‖)) * (‖oneI ι a‖ + ‖L‖) ^ 2, 2, fun y => ?_⟩
    obtain ⟨h1, h2⟩ := e_gI_u_norm hu hu' y
    set c := ‖oneI ι a‖ + ‖L‖
    have hc0 : 0 ≤ c := by positivity
    rw [Complex.norm_real]
    have e1 : ‖(e_b ι a).coord i (mulI (gI (u y)⁻¹) (mulI Z (gI (u y))))‖ ≤
        ‖e_crd (ι := ι) (a := a) i‖ * ‖mulI (gI (u y)⁻¹) (mulI Z (gI (u y)))‖ :=
      (e_crd (ι := ι) (a := a) i).le_opNorm _
    have e2 := hK (gI (u y)⁻¹) (mulI Z (gI (u y)))
    have e3 := hK Z (gI (u y))
    have hcrd := norm_nonneg (e_crd (ι := ι) (a := a) i)
    calc _ ≤ ‖e_crd (ι := ι) (a := a) i‖ * (K * ‖gI (u y)⁻¹‖ * (K * ‖Z‖ * ‖gI (u y)‖)) := by
          refine e1.trans (mul_le_mul_of_nonneg_left (e2.trans ?_) hcrd)
          exact mul_le_mul_of_nonneg_left e3 (by positivity)
      _ ≤ ‖e_crd (ι := ι) (a := a) i‖ * (K * (c * (1 + ‖y‖)) * (K * ‖Z‖ * (c * (1 + ‖y‖)))) := by
          gcongr
      _ = _ := by ring

theorem key [CompleteSpace X] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (hρ : PolyBd ρ) {u : V → GL (Fin a) (ι → ℂ)} {L : V →L[ℝ] LieI ι a}
    (hu : ∀ y, (u y).val = 1 + Matrix.of (L y)) (hu' : ∀ y, (u y)⁻¹.val = 1 - Matrix.of (L y))
    {𝒢 : Submodule ℂ (V → X)} (h𝒢 : RapidFam ρ 𝒢)
    (hmul : ∀ H ∈ 𝒢, ∀ m : V → ℂ, PolyG m → (fun y => m y • H y) ∈ 𝒢) {H : V → X} (hH : H ∈ 𝒢) :
    ∃ Dv : LieI ι a →L[ℝ] X, HasFDerivAt (orb ρ (∫ y, ρ (u y) (H y) ∂μ)) Dv (oneI ι a) ∧
      ∀ Z, ∃ H' ∈ 𝒢, Dv Z = ∫ y, ρ (u y) (H' y) ∂μ := by
  classical
  obtain ⟨hHc, hHr, D, hD𝒢, hD'⟩ := h𝒢 H hH
  have hDy : ∀ y, HasFDerivAt (orb ρ (H y)) (e_Dy D y) (oneI ι a) := fun y => by
    obtain ⟨D', h1, h2⟩ := hD' y
    rwa [← e_Dy_eq D y D' h1]
  have hrap : ∀ W ∈ 𝒢, Rap (fun y => ρ (u y) (W y)) := fun W hW => by
    obtain ⟨hc, hr, D1, -, hD1⟩ := h𝒢 W hW
    exact rap_rho hρ hu hu' ⟨hc, hr⟩ fun y => (hD1 y).elim fun D' h => ⟨D', h.2⟩
  have hint : Integrable (fun y => ρ (u y) (H y)) μ := integrable_of_rap μ (hrap H hH)
  let F : LieI ι a → V → X := fun M y => orb ρ (H y) (mulI M (gI (u y)))
  have hFe : ∀ M y, F M y = unitChartOperator ρ M (ρ (u y) (H y)) := fun M y => by
    show orb ρ (H y) (mulI M (gI (u y))) = _
    rw [orb_mulI_right, e_orb_eq]
  have hformula : orb ρ (∫ y, ρ (u y) (H y) ∂μ) = fun M => ∫ y, F M y ∂μ := by
    funext M; simp only [hFe, e_orb_eq]; exact ((unitChartOperator ρ M).integral_comp_comm hint).symm
  let F' : LieI ι a → V → (LieI ι a →L[ℝ] X) := fun M y =>
    if h : IsUnit (Matrix.of M) then
      (((ρ (h.unit * u y)).restrictScalars ℝ).comp ((e_Dy D y).comp (lmul (gI (h.unit * u y)⁻¹)))).comp
        (rmul (gI (u y)))
    else 0
  have hF'g : ∀ g y, F' (gI g) y = (((ρ (g * u y)).restrictScalars ℝ).comp
      ((e_Dy D y).comp (lmul (gI (g * u y)⁻¹)))).comp (rmul (gI (u y))) := by
    intro g y
    simp only [F', dif_pos (e_isUnit_gI g), e_unit_gI g]
  have hdiff : ∀ g y, HasFDerivAt (F · y) (F' (gI g) y) (gI g) := by
    intro g y
    rw [hF'g]
    have h1 := hasFDerivAt_orb_at ρ (hDy y) (g * u y)
    have e : gI (g * u y) = rmul (gI (u y)) (gI g) := (mulI_gI g (u y)).symm
    rw [e] at h1
    exact h1.comp (gI g) (rmul (gI (u y))).hasFDerivAt
  obtain ⟨K, hK0, hK⟩ := exists_mulI_bound (ι := ι) (a := a)
  obtain ⟨ε, hε, B0, hB⟩ := exists_inv_bound (ι := ι) (a := a)
  obtain ⟨C, N, hC0, hC⟩ := polyBd_opNorm ρ hρ
  obtain ⟨B, hB0, hBB⟩ : ∃ B : ℝ, 0 ≤ B ∧ B0 ≤ B := ⟨max B0 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨c, hc0, hcu⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, ‖gI (u y)‖ ≤ c * (1 + ‖y‖) ∧ ‖gI (u y)⁻¹‖ ≤ c * (1 + ‖y‖) :=
    ⟨_, by positivity, e_gI_u_norm hu hu'⟩
  obtain ⟨A, hA0, hAM⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ M ∈ Metric.ball (oneI ι a) ε, ‖M‖ ≤ A := by
    refine ⟨‖oneI ι a‖ + ε, by positivity, fun M hM => ?_⟩
    have h1 := mem_ball_iff_norm.1 hM
    have h2 := norm_sub_norm_le M (oneI ι a)
    linarith
  let bound : V → ℝ := fun y => (C * (1 + K * A * c + K * c * B) ^ N * (K * (K * c * B)) * (K * c)) *
    ∑ i, ‖e_crd (ι := ι) (a := a) i‖ * ((1 + ‖y‖) ^ (N + 2) * ‖D (e_b ι a i) y‖)
  have hbound : ∀ y, ∀ M ∈ Metric.ball (oneI ι a) ε, ‖F' M y‖ ≤ bound y := by
    intro y M hM
    have hgA := hAM M hM
    obtain ⟨g, rfl, hg⟩ := hB M hM
    have hgB : ‖gI g⁻¹‖ ≤ B := hg.trans hBB
    obtain ⟨hu1, hu2⟩ := hcu y
    have ht1 : 1 ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
    have n1 : ‖gI (g * u y)‖ ≤ K * A * (c * (1 + ‖y‖)) := by
      rw [← mulI_gI]; refine (hK _ _).trans ?_; gcongr
    have n2 : ‖gI (g * u y)⁻¹‖ ≤ K * (c * (1 + ‖y‖)) * B := by
      rw [_root_.mul_inv_rev, ← mulI_gI]; refine (hK _ _).trans ?_; gcongr
    have nρ : ‖ρ (g * u y)‖ ≤ C * ((1 + K * A * c + K * c * B) * (1 + ‖y‖)) ^ N := by
      refine (hC _).trans ?_
      gcongr
      calc 1 + ‖gI (g * u y)‖ + ‖gI (g * u y)⁻¹‖
          ≤ (1 + ‖y‖) + K * A * (c * (1 + ‖y‖)) + K * (c * (1 + ‖y‖)) * B := by linarith
        _ = (1 + K * A * c + K * c * B) * (1 + ‖y‖) := by ring
    have nl : ‖lmul (gI (g * u y)⁻¹)‖ ≤ K * (K * (c * (1 + ‖y‖)) * B) :=
      (e_lmul_norm hK0 hK _).trans (by gcongr)
    have nr : ‖rmul (gI (u y))‖ ≤ K * (c * (1 + ‖y‖)) := (e_rmul_norm hK0 hK _).trans (by gcongr)
    have nD := e_Dy_norm D y
    have hS : ∑ i, ‖e_crd (ι := ι) (a := a) i‖ * ((1 + ‖y‖) ^ (N + 2) * ‖D (e_b ι a i) y‖) =
        (1 + ‖y‖) ^ (N + 2) * ∑ i, ‖e_crd (ι := ι) (a := a) i‖ * ‖D (e_b ι a i) y‖ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hF'g]
    calc _ ≤ ‖ρ (g * u y)‖ * (‖e_Dy D y‖ * ‖lmul (gI (g * u y)⁻¹)‖) * ‖rmul (gI (u y))‖ := by
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          gcongr
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          rw [ContinuousLinearMap.norm_restrictScalars]
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * ((1 + K * A * c + K * c * B) * (1 + ‖y‖)) ^ N) *
            ((∑ i, ‖e_crd (ι := ι) (a := a) i‖ * ‖D (e_b ι a i) y‖) * (K * (K * (c * (1 + ‖y‖)) * B))) *
            (K * (c * (1 + ‖y‖))) := by
          gcongr
      _ = bound y := by
          simp only [bound]; rw [hS, mul_pow]; ring
  have hbi : Integrable bound μ := by
    refine Integrable.const_mul (integrable_finsetSum _ fun i _ => Integrable.const_mul ?_ _) _
    obtain ⟨hc, hr, -⟩ := h𝒢 _ (hD𝒢 (e_b ι a i))
    exact integrable_of_rap μ (e_rap_weight ⟨hc, hr⟩ (N + 2))
  let H' : LieI ι a → V → X := fun Z y =>
    ∑ i, (((e_b ι a).coord i (mulI (gI (u y)⁻¹) (mulI Z (gI (u y)))) : ℝ) : ℂ) • D (e_b ι a i) y
  have hH' : ∀ Z, H' Z ∈ 𝒢 := fun Z => by
    have : H' Z = ∑ i, (fun y => (((e_b ι a).coord i (mulI (gI (u y)⁻¹) (mulI Z (gI (u y)))) : ℝ) : ℂ) •
        D (e_b ι a i) y) := by
      funext y; simp [H', Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => hmul _ (hD𝒢 _) _ (e_polyG_coord hu hu' Z i)
  have hF'Z : ∀ y Z, F' (oneI ι a) y Z = ρ (u y) (H' Z y) := by
    intro y Z
    rw [← gI_one, hF'g]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', lmul_apply,
      rmul_apply, one_mul, e_Dy_apply, H']
  have hF'c : Continuous (F' (oneI ι a)) := by
    refine continuous_clm_apply.2 fun Z => ?_
    simp_rw [hF'Z]
    exact (hrap _ (hH' Z)).1
  have hFc : ∀ M, Continuous (F M) := fun M => by
    have : F M = fun y => unitChartOperator ρ M (ρ (u y) (H y)) := funext (hFe M)
    rw [this]; exact (unitChartOperator ρ M).continuous.comp (hrap H hH).1
  have hF1 : Integrable (F (oneI ι a)) μ := by
    have : F (oneI ι a) = fun y => unitChartOperator ρ (oneI ι a) (ρ (u y) (H y)) := funext (hFe _)
    rw [this]; exact (unitChartOperator ρ _).integrable_comp hint
  have hmem : oneI ι a ∈ Metric.ball (oneI ι a) ε := Metric.mem_ball_self hε
  have hF'int : Integrable (F' (oneI ι a)) μ :=
    Integrable.mono' hbi hF'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => hbound y _ hmem)
  have hdiffb : ∀ y, ∀ M ∈ Metric.ball (oneI ι a) ε, HasFDerivAt (F · y) (F' M y) M := by
    intro y M hM; obtain ⟨g, rfl, -⟩ := hB M hM; exact hdiff g y
  refine ⟨∫ y, F' (oneI ι a) y ∂μ, ?_, fun Z => ⟨H' Z, hH' Z, ?_⟩⟩
  · rw [hformula]
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds _ hε)
      (Filter.Eventually.of_forall fun M => (hFc M).aestronglyMeasurable) hF1 hF'c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hbound y) hbi (Filter.Eventually.of_forall fun y => hdiffb y)
  · rw [ContinuousLinearMap.integral_apply hF'int]
    simp only [hF'Z]

end KeyMain

end Fe

end UnitChartOperator

theorem unit_chart_operator_bound : S1 → S3 := by
  intro hS1 ι _ a X _ _ _ ρ hρ V _ _ _ _ _ μ _ u L hu hu' 𝒢 h𝒢 G hG
  have h1 : RapidFam ρ (UnitChartOperator.Mult 𝒢) := UnitChartOperator.rapidFam_mult h𝒢
  have hint : ∀ H ∈ UnitChartOperator.Mult 𝒢, Integrable (fun y => ρ (u y) (H y)) μ := by
    intro H hH
    obtain ⟨hc, hr, D, -, hD⟩ := h1 H hH
    refine UnitChartOperator.integrable_of_rap μ (UnitChartOperator.rap_rho hρ hu hu' ⟨hc, hr⟩ fun y => ?_)
    obtain ⟨D', -, h⟩ := hD y
    exact ⟨D', h⟩
  refine ⟨hint G (UnitChartOperator.mem_mult hG), ?_⟩
  let S0 : Set X := {x | ∃ H ∈ UnitChartOperator.Mult 𝒢, x = ∫ y, ρ (u y) (H y) ∂μ}
  refine hS1 ι a X ρ hρ (Submodule.span ℂ S0) ?_ _ (Submodule.subset_span ⟨G, UnitChartOperator.mem_mult hG, rfl⟩)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨H, hH, rfl⟩ := hx
    obtain ⟨Dv, hDv, hZ⟩ := UnitChartOperator.key μ hρ hu hu' h1 (fun H hH m hm => UnitChartOperator.mult_mul hH hm) hH
    refine ⟨Dv, hDv, fun Z => ?_⟩
    obtain ⟨H', hH', e⟩ := hZ Z
    exact Submodule.subset_span ⟨H', hH', e⟩
  | zero =>
    refine ⟨0, ?_, fun Z => Submodule.zero_mem _⟩
    rw [UnitChartOperator.orb_zero]
    exact hasFDerivAt_const _ _
  | add x y _ _ hx hy =>
    obtain ⟨Dx, hx1, hx2⟩ := hx
    obtain ⟨Dy, hy1, hy2⟩ := hy
    refine ⟨Dx + Dy, ?_, fun Z => Submodule.add_mem _ (hx2 Z) (hy2 Z)⟩
    rw [UnitChartOperator.orb_add]
    exact hx1.add hy1
  | smul c x _ hx =>
    obtain ⟨Dx, hx1, hx2⟩ := hx
    refine ⟨c • Dx, ?_, fun Z => Submodule.smul_mem _ c (hx2 Z)⟩
    rw [UnitChartOperator.orb_smul]
    exact hx1.const_smul c

end PositivityTheory.jumpWindows

end
