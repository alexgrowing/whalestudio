import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.AssemblyStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnipotentExpHaarSqrtBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiDecayCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HWExists

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

namespace Asm

variable {k r : ℕ}

theorem cay_unit {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) :
    P * P⁻¹ = 1 ∧ P⁻¹ * P = 1 := by
  have h := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  exact ⟨Matrix.mul_nonsing_inv P h, Matrix.nonsing_inv_mul P h⟩

theorem cay_left {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) :
    Pᴴ * Jm ε = Formalism.QuantumDeterminants.Hpk k r * P⁻¹ := by
  have h1 := (cay_unit hP).1
  rw [← hP.2, Matrix.mul_assoc (Pᴴ * Formalism.REAL.Jm ε), h1, Matrix.mul_one]
  rfl

theorem cay_right {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) :
    Jm ε * P = (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
  have h1 := (cay_unit hP).1
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [← hP.2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rfl

theorem cay_mem {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {g : Mat k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : inUJ ε (P * g * P⁻¹) := by
  have h1 := (cay_unit hP).1
  have hR := cay_right hP
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hPJP : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  show (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹) = Jm ε
  calc (P * g * P⁻¹)ᴴ * Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by
        rw [hPJP, hg', ← hR, Matrix.mul_assoc, h1, Matrix.mul_one]

open scoped Matrix.Norms.Operator in

theorem cay_inG {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) : inG ε (P * Y * P⁻¹) := by
  have hL := cay_left hP
  have hR := cay_right hP
  set H := Formalism.QuantumDeterminants.Hpk k r with hH
  have hlie : Yᴴ * H + H * Y = 0 := by
    have hc : ∀ t : ℝ, NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y) = H := by
      intro t
      have h : (NormedSpace.exp ((t : ℂ) • Y))ᴴ * H * NormedSpace.exp ((t : ℂ) • Y) = H :=
        (hY t).1
      have e1 : (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (t • Yᴴ) := by
        rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def,
          Complex.conj_ofReal, Complex.coe_smul]
      rw [← e1, ← Complex.coe_smul]
      exact h
    have hd1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Yᴴ (0 : ℝ)
    have hd2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (0 : ℝ)
    have hf := (hd1.mul_const H).mul hd2
    have h0 := hf.unique ((hasDerivAt_const (0 : ℝ) H).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => hc t))
    simpa using h0
  show (P * Y * P⁻¹)ᴴ * Jm ε + Jm ε * (P * Y * P⁻¹) = 0
  calc (P * Y * P⁻¹)ᴴ * Jm ε + Jm ε * (P * Y * P⁻¹)
      = (P⁻¹)ᴴ * Yᴴ * (Pᴴ * Jm ε) + (Jm ε * P) * Y * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Yᴴ * H + H * Y) * P⁻¹ := by
        rw [hL, hR]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hlie, Matrix.mul_zero, Matrix.zero_mul]

theorem conj_sum_sub {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    starRingEnd ℂ (∑ i ∈ s, (a i - starRingEnd ℂ (a i))) = -∑ i ∈ s, (a i - starRingEnd ℂ (a i)) := by
  rw [map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, Complex.conj_conj, neg_sub]

theorem re_sum_sub {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∑ i ∈ s, (a i - starRingEnd ℂ (a i))).re = 0 := by
  rw [Complex.re_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Complex.sub_re, Complex.conj_re, sub_self]

theorem hs_nonneg {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ S7.hs X := by
  unfold S7.hs
  positivity

theorem hs_unreal {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    S7.hs (Formalism.MainNotions.S.unrealify x) = ‖x‖ ^ 2 := by
  unfold S7.hs
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [Formalism.MainNotions.S.unrealify, Complex.sq_norm, Complex.normSq_mk, Real.norm_eq_abs, sq_abs]
  ring

theorem eight_n_q0_lt_needed_gap {n : ℕ} (ε : Fin n → Bool) : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < hNeed ε := by
  have hq : ((S7.q0 ε : ℕ) : ℝ) = min (pOf ε : ℝ) (qOf ε : ℝ) := by
    simp [S7.q0]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ min (pOf ε : ℝ) (qOf ε : ℝ) :=
    le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hs : 0 ≤ Real.sqrt (2 * min (pOf ε : ℝ) (qOf ε : ℝ)) := Real.sqrt_nonneg _
  have hnm := mul_nonneg hn hm
  rw [hq]
  unfold hNeed
  refine lt_max_of_lt_right (lt_max_of_lt_left ?_)
  nlinarith

theorem stdGap_of {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hG : GapLap ε lam h) :
    StdGap ε lam := by
  obtain ⟨h1, h2, h3⟩ := hG
  refine ⟨h1, h, h2, lt_trans ?_ h3⟩
  unfold hNeed
  refine lt_max_of_lt_left ?_
  have := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
  linarith

theorem norm_inner_w {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (A : T.V →L[ℂ] T.V) :
    ‖⟪T.w, A T.w⟫_ℂ‖ ≤ ‖A‖ := by
  calc ‖⟪T.w, A T.w⟫_ℂ‖ ≤ ‖T.w‖ * ‖A T.w‖ := norm_inner_le_norm _ _
    _ ≤ ‖T.w‖ * (‖A‖ * ‖T.w‖) := by gcongr; exact A.le_opNorm _
    _ = ‖A‖ := by rw [T.w_norm]; ring

def chart (k r : ℕ) (x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j

theorem exp_mat_continuous : Continuous (NormedSpace.exp : Mat k r → Mat k r) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem unreal_continuous :
    Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) : Mat k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h1 : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, false) :=
    (EuclideanSpace.proj (i, j, false)).continuous.comp continuous_subtype_val
  have h2 : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, true) :=
    (EuclideanSpace.proj (i, j, true)).continuous.comp continuous_subtype_val
  have h3 : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      ((x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, false) : ℂ) +
        ((x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) (i, j, true) : ℂ) *
          Complex.I :=
    (Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)
  refine h3.congr fun x => ?_
  apply Complex.ext <;> simp [Formalism.MainNotions.S.unrealify]

theorem exp_unreal_continuous :
    Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      (NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) : Mat k r) :=
  exp_mat_continuous.comp unreal_continuous

theorem chart_embedding
    (hinj : ∀ Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r), ∀ Y' ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r),
      NormedSpace.exp Y = NormedSpace.exp Y' → Y = Y')
    (hunr : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    MeasurableEmbedding (chart k r) := by
  have hcont : Continuous (chart k r) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp exp_unreal_continuous)
  refine hcont.measurableEmbedding ?_
  intro x y hxy
  have h1 : NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) =
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) := by
    ext i j
    exact congrFun (congrFun hxy i) j
  have h2 := hinj _ (hunr x) _ (hunr y) h1
  exact Subtype.ext ((unrealL (2 * r + k + 1)).injective h2)

def partNML {n : ℕ} (ε : Fin n → Bool) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := partNM ε d
  map_add' X Y := by
    ext a b; simp only [partNM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext a b; simp only [partNM, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def bracketB {n : ℕ} (ε : Fin n → Bool) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun X Y => -(1 / 2 : ℂ) * trace (dMat d * (X * partNML ε d Y - partNML ε d Y * X)))
    (fun X X' Y => by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]; ring)
    (fun c X Y => by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul,
        Complex.real_smul]; ring)
    (fun X Y Y' => by
      simp only [map_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add,
        Matrix.trace_sub]; ring)
    (fun c X Y => by
      simp only [map_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_sub,
        Matrix.trace_smul, Complex.real_smul]; ring)

def conjL (P : Mat k r) : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) →ₗ[ℝ] Mat k r :=
  (LinearMap.mulRight ℝ P⁻¹).comp ((LinearMap.mulLeft ℝ P).comp
    ((unrealL (2 * r + k + 1)).toLinearMap.comp (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)).subtype))

theorem conjL_apply (P : Mat k r) (x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) :
    conjL P x = P * Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) * P⁻¹ := rfl

theorem bracketB_apply {n : ℕ} (ε : Fin n → Bool) (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    bracketB ε d X X = qForm ε d X / 2 := by
  show -(1 / 2 : ℂ) * trace (dMat d * (X * partNM ε d X - partNM ε d X * X)) = qForm ε d X / 2
  unfold qForm
  ring

end Asm

open Asm in
theorem assembly : AssemblyStatement := by
  intro hB1 hB3 hB4 hB5 hB6 hB7a hB7b hLamT hPsi hLink
  intro k r u v b hk hHC hIl hH
  obtain ⟨huHC, hq0, hlin, hWwt, t₁, ht₁⟩ := hLamT k r u v b hk hHC hIl hH
  obtain ⟨P, hP, hPW, htr, hpsi⟩ := hB1 k r hk
  obtain ⟨hinj, -, hunr, hNhaar, -⟩ := hB4 k r
  obtain ⟨c5, hc5, hmaj⟩ := hB5 k r (parEps k r) P hP
  obtain ⟨μW, hμW, hμW1⟩ := hB7a k r
  obtain ⟨Hπ, iπ1, iπ2, π', hπ'⟩ := HW.highest_weight_exists k u huHC
  have hT : ∀ t : ℕ, t₁ ≤ t →
      Nonempty (S7.KType (parEps k r) (lowK (parEps k r) (lamT k r u b t))) :=
    fun t ht => HW.kType_exists _ _ (ht₁ t ht).1
  have hMu : ∀ t : ℕ, t₁ ≤ t → ∃ μ : Fin (2 * r + k + 1) → ℤ, S7.IsMu (lamT k r u b t) μ := by
    intro t ht
    choose m hm using (ht₁ t ht).1.2
    refine ⟨fun a => m a + (((2 * r + k + 1 : ℕ) : ℤ) - 1 - ((a : ℕ) : ℤ)), fun a => ?_⟩
    have h1 := hm a
    simp only [rho]
    push_cast at h1 ⊢
    linarith
  choose μ hμ using hMu

  have hGap : ∀ t (ht : t₁ ≤ t), GapAtLeast (parEps k r) (lamT k r u b t) ((t : ℝ) / 2) :=
    fun t ht => (ht₁ t ht).2.2.1
  have h8 : ∀ t (ht : t₁ ≤ t), 8 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 (parEps k r) : ℝ) < (t : ℝ) / 2 :=
    fun t ht => (eight_n_q0_lt_needed_gap _).trans (ht₁ t ht).2.2.2
  have hPF : ∀ t (ht : t₁ ≤ t), IsPsiFor (parEps k r) (lamT k r u b t) (Classical.choice (hT t ht))
      (S7.PsiM (Classical.choice (hT t ht)) (μ t ht)) ∧
      ContinuousOn (S7.PsiM (Classical.choice (hT t ht)) (μ t ht)) (UJset (parEps k r)) :=
    fun t ht => hPsi _ _ _ _ _ _ (ht₁ t ht).1 (hμ t ht) (hGap t ht) hq0 (h8 t ht)

  have hU : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _) ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r) := hunr
  have hexpN : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) ∈ Formalism.QuantumDeterminants.Nset k r := by
    intro x; simpa using hU x 1
  have hgU : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹ ∈ UJset (parEps k r) :=
    fun x => cay_mem hP (hexpN x).1
  have hτre : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      (trace (dMat (dNode k r) * conjL P x)).re = 0 := by
    intro x; rw [conjL_apply, htr _ (hU x)]; exact re_sum_sub _ _
  have hτconj : ∀ x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r),
      starRingEnd ℂ (trace (dMat (dNode k r) * conjL P x)) = -trace (dMat (dNode k r) * conjL P x) := by
    intro x; rw [conjL_apply, htr _ (hU x)]; exact conj_sum_sub _ _
  have hτc : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) => trace (dMat (dNode k r) * conjL P x) :=
    (continuous_const.matrix_mul ((continuous_const.matrix_mul unreal_continuous).matrix_mul
      continuous_const)).matrix_trace

  let f : ℕ → Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) → ℂ := fun t x =>
    if ht : t₁ ≤ t then
      ⟪(Classical.choice (hT t ht)).w, S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
          (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹)
          (Classical.choice (hT t ht)).w⟫_ℂ *
        Complex.exp (-((t : ℂ) * trace (dMat (dNode k r) * conjL P x)))
    else 0
  have hfe : ∀ t (ht : t₁ ≤ t) x, f t x =
      ⟪(Classical.choice (hT t ht)).w, S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
          (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹)
          (Classical.choice (hT t ht)).w⟫_ℂ *
        Complex.exp (-((t : ℂ) * trace (dMat (dNode k r) * conjL P x))) :=
    fun t ht x => dif_pos ht
  have hgc : Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹ :=
    (continuous_const.matrix_mul exp_unreal_continuous).matrix_mul continuous_const
  have hPc : ∀ t (ht : t₁ ≤ t), Continuous fun x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r) =>
      S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
        (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹) :=
    fun t ht => (hPF t ht).2.comp_continuous hgc hgU
  have hfc : ∀ t (ht : t₁ ≤ t), Continuous (f t) := by
    intro t ht
    have : f t = fun x => _ := funext (hfe t ht)
    rw [this]
    exact (continuous_const.inner ((hPc t ht).clm_apply continuous_const)).mul
      (Complex.continuous_exp.comp (continuous_const.mul hτc).neg)

  have hbound : ∀ t (ht : t₁ ≤ t) (x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)),
      ‖S7.PsiM (Classical.choice (hT t ht)) (μ t ht)
          (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) * P⁻¹)‖ ≤
        (1 + ‖x‖ ^ 2) ^ (-(c5 / 16 * (t : ℝ))) := by
    intro t ht x
    obtain ⟨κ, X, hX, hkX⟩ := S7.polar_exists (hgU x)
    have hdec := S7.psiM_dec (Classical.choice (hT t ht)) (μ t ht) (hμ t ht) (ht₁ t ht).1 (hGap t ht)
      hq0 κ hX
    have hm := hmaj _ (hU x) κ X hX hkX
    rw [hs_unreal] at hm
    have hxn : ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ = ‖x‖ := rfl
    rw [hxn] at hm
    rw [hkX]
    refine hdec.trans ?_
    have h1p : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [Real.rpow_def_of_pos h1p]
    apply Real.exp_le_exp.mpr
    have h2 := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ (t : ℝ) / 16 by positivity)
    nlinarith [h2]
  have hbd : ∀ᶠ t : ℕ in atTop, ∀ x, ‖f t x‖ ≤ (1 + 1 * ‖x‖ ^ 2) ^ (-(c5 / 16 * (t : ℝ))) := by
    filter_upwards [eventually_ge_atTop t₁] with t ht x
    rw [hfe t ht x, one_mul, norm_mul, Complex.norm_exp]
    have hre : (-((t : ℂ) * trace (dMat (dNode k r) * conjL P x))).re = 0 := by
      simp [Complex.mul_re, hτre x]
    rw [hre, Real.exp_zero, mul_one]
    exact (norm_inner_w _ _).trans (hbound t ht x)

  let B := (bracketB (parEps k r) (dNode k r)).compl₁₂ (conjL P) (conjL P)
  have hBx : ∀ x, B x x = qForm (parEps k r) (dNode k r) (conjL P x) / 2 :=
    fun x => bracketB_apply _ _ _
  have hlim : ∀ x, Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • x)) atTop
      (𝓝 (Complex.exp (-(B x x)))) := by
    intro x
    obtain ⟨C, hC⟩ := hB3 (2 * r + k + 1) (parEps k r) (dNode k r) (lowK (parEps k r) (lamT k r u b 0))
      (Real.sqrt (S7.hs (conjL P x)))
    have hlimC : Tendsto (fun t : ℕ => C / Real.sqrt t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlimC
    filter_upwards [eventually_ge_atTop t₁, eventually_ge_atTop 1] with t ht ht1
    have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    obtain ⟨H, i1, i2, σ, w, hsm, hcoef⟩ := hLink _ _ _ (Classical.choice (hT t ht))
      (S7.PsiM (Classical.choice (hT t ht)) (μ t ht)) (stdGap_of (ht₁ t ht).2) (hPF t ht).1
    have hY := cay_inG hP (hU x)
    have hB3' := hC t ht1' H σ _ w hsm (hlin t) (conjL P x) hY (Real.sq_sqrt (hs_nonneg _)).symm.le
    have hus : Formalism.MainNotions.S.unrealify
        ((((Real.sqrt t)⁻¹ • x : Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r))) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) =
        ((((Real.sqrt t)⁻¹ : ℝ) : ℂ)) • Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) := by
      rw [Submodule.coe_smul, Complex.coe_smul]
      exact (unrealL (2 * r + k + 1)).map_smul _ _
    have hcj : P * NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) *
        P⁻¹ = NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • conjL P x) := by
      rw [← Matrix.exp_conj _ _ hP.1, conjL_apply, Matrix.mul_smul, Matrix.smul_mul]
    have hmem : NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • conjL P x) ∈ UJset (parEps k r) := by
      rw [← hcj]; exact cay_mem hP (hU x _).1
    have hτs : trace (dMat (dNode k r) * conjL P ((Real.sqrt t)⁻¹ • x)) =
        (((Real.sqrt t)⁻¹ : ℝ) : ℂ) * trace (dMat (dNode k r) * conjL P x) := by
      rw [map_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul]
    have hts : (t : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := by
      have h := Real.div_sqrt (x := (t : ℝ))
      rw [div_eq_mul_inv] at h
      exact_mod_cast h
    have hfx : f t ((Real.sqrt t)⁻¹ • x) =
        ⟪w, σ (NormedSpace.exp ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • conjL P x)) w⟫_ℂ *
          Complex.exp (-((Real.sqrt t : ℂ) * trace (dMat (dNode k r) * conjL P x))) := by
      rw [hfe t ht, hus, hcj, ← hcoef _ hmem, hτs, ← mul_assoc, hts]
    rw [hfx, hBx, show -(qForm (parEps k r) (dNode k r) (conjL P x) / 2) =
      -qForm (parEps k r) (dNode k r) (conjL P x) / 2 by ring]
    exact hB3'

  have hm : ∀ᶠ t : ℕ in atTop, AEStronglyMeasurable (f t) volume := by
    filter_upwards [eventually_ge_atTop t₁] with t ht
    exact (hfc t ht).aestronglyMeasurable
  have hγ : 0 < c5 / 16 := by positivity
  have hev := hB6 (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) volume f hm B hlim one_pos hγ hbd
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt
    ((Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) : ℝ) / (2 * (c5 / 16)))
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop (max (max t₁ N₂) 1)))
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨⟨-, hne⟩, htm⟩ := ht₀ t ht
  have htt : t₁ ≤ t := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) htm)
  have htN : N₂ ≤ t := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) htm)
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) htm

  haveI : Nontrivial Hπ := hπ'.1
  haveI hFD : FiniteDimensional ℂ Hπ := hπ'.2.1
  haveI hCS : CompleteSpace Hπ := FiniteDimensional.complete ℂ Hπ
  let πm : Mat k r → (Hπ →L[ℂ] Hπ) := fun g =>
    π' (Matrix.of fun i j : Fin k => g (Formalism.QuantumDeterminants.wI k r i.castSucc) (Formalism.QuantumDeterminants.wI k r j.castSucc))
  have hblk : ∀ h : Matrix (Fin k) (Fin k) ℂ, πm (Formalism.MainNotions.S.blockW k r h) = π' h := by
    intro h
    show π' _ = π' h
    congr 1
    ext i j
    simp [Formalism.MainNotions.S.blockW, Formalism.QuantumDeterminants.wI]
  have hπb : (fun h => πm (Formalism.MainNotions.S.blockW k r h)) = π' := funext hblk
  have hHCU : Formalism.MainNotions.S.IsHCTypeU k u (fun h => πm (Formalism.MainNotions.S.blockW k r h)) := by rw [hπb]; exact hπ'
  obtain ⟨v0, -, hv0, hwt⟩ := hπ'.2.2.2.2.2.2.1
  let ξ : Hπ := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0
  have hξn : ‖ξ‖ = 1 := by
    simp only [ξ]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  have hξw : Formalism.MainNotions.S.IsWtOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) (fun h => πm (Formalism.MainNotions.S.blockW k r h))
      (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos k) u) ξ := by
    rw [hπb]
    intro θ _
    have hθK : Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext a
        rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]
        simp
      · simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal]
        congr 1
        funext a
        ring
    simp only [ξ]
    rw [ContinuousLinearMap.map_smul, hwt θ hθK, smul_comm]

  have hinWb : Formalism.QuantumDeterminants.inWb k r (z0 k r) := by
    intro i hi
    show (Pi.single (Formalism.QuantumDeterminants.wI k r (Fin.last k)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = 0
    rw [Pi.single_apply, if_neg]
    intro hh
    subst hh
    simp only [Formalism.QuantumDeterminants.wI, Fin.val_last] at hi
    omega
  have key : ∀ (H : Mat k r) (i : Fin (2 * r + k + 1)),
      Formalism.QuantumDeterminants.herm H (Formalism.QuantumDeterminants.bvec i) (Formalism.QuantumDeterminants.bvec i) = H i i := by
    intro H i
    rw [show Formalism.QuantumDeterminants.herm H (Formalism.QuantumDeterminants.bvec i) (Formalism.QuantumDeterminants.bvec i) =
      ∑ j, star (Formalism.QuantumDeterminants.bvec i j) * (H *ᵥ Formalism.QuantumDeterminants.bvec i) j from rfl]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hj]) (by simp)]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hTz1 : Formalism.QuantumDeterminants.Tz k r (z0 k r) = 1 := by
    rw [Formalism.QuantumDeterminants.Tz, z0, key]
    simp [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.wI]
  have hone : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  have hframe : Formalism.MainNotions.S.IsFrameW k r (z0 k r) 1 := by
    refine ⟨hone, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, ?_⟩
    rw [Matrix.one_mulVec, hTz1, Real.sqrt_one]
    simp [z0]
  have hHCW : Formalism.MainNotions.S.IsHCTypeW k r (z0 k r) u πm := by
    refine ⟨1, hframe, ?_⟩
    have : (fun h => πm (1 * Formalism.MainNotions.S.blockW k r h * 1⁻¹)) = fun h => πm (Formalism.MainNotions.S.blockW k r h) := by
      funext h; rw [inv_one, Matrix.mul_one, Matrix.one_mul]
    rw [this]; exact hHCU
  have hcne : ∀ a, cBase r (t : ℝ) a ≠ 0 := by
    intro a
    have : (t : ℂ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
    simp [cBase, Complex.I_ne_zero, this]

  have hemb := chart_embedding hinj hU
  have hμN : Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1 = Measure.map (chart k r) volume := by
    rw [Formalism.MainNotions.S.haarLie, one_smul]; rfl
  have hI : ∫ m, psiCoef (Classical.choice (hT t htt)) (μ t htt) P (Classical.choice (hT t htt)).w
        (Classical.choice (hT t htt)).w (Matrix.of m) *
        starRingEnd ℂ (Formalism.MainNotions.S.psiGen k r (z0 k r) (cBase r t) (Matrix.of m))
        ∂(Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) = ∫ x, f t x := by
    rw [hμN, hemb.integral_map]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [hfe t htt x]
    show ⟪(Classical.choice (hT t htt)).w, S7.PsiM (Classical.choice (hT t htt)) (μ t htt)
        (P * NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) * P⁻¹)
        (Classical.choice (hT t htt)).w⟫_ℂ *
        starRingEnd ℂ (Formalism.MainNotions.S.psiGen k r (z0 k r) (cBase r t)
          (NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))))) = _
    congr 1
    rw [hpsi _ (hU x) (t : ℝ), ← Complex.exp_conj, map_mul, Complex.conj_ofReal, ← conjL_apply, hτconj x]
    congr 1
    push_cast
    ring
  have hint2 : Integrable (fun m : Formalism.QuantumDeterminants.Mt k r =>
      ‖S7.PsiM (Classical.choice (hT t htt)) (μ t htt) (P * Matrix.of m * P⁻¹)‖)
      (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) := by
    rw [hμN, hemb.integrable_map_iff]
    have hfr : (Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.QuantumDeterminants.Nset k r)) : ℝ) < 2 * (c5 / 16) * t := by
      have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (c5 / 16))).mp hN₂
      have h2 : (N₂ : ℝ) ≤ t := by exact_mod_cast htN
      nlinarith
    refine Integrable.mono' (integrable_rpow_neg_one_add_norm_sq (μ := volume) hfr)
      ((hPc t htt).norm.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Function.comp_apply, norm_norm]
    exact (hbound t htt x).trans (le_of_eq (by congr 1; ring))
  have h7 := hB7b k r (parEps k r) (lowK (parEps k r) (lamT k r u b t)) (Classical.choice (hT t htt))
    (μ t htt) P u (cBase r t) Hπ πm ξ μW (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1) hk hP hPW hHCU hξn
    hξw (hWwt t) hμW hμW1 hNhaar.1 (hPF t htt).2 hint2
  refine ⟨Classical.choice (hT t htt), μ t htt, P, z0 k r, cBase r t, Hπ, iπ1, iπ2, hCS, πm, μW,
    Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1, hμ t htt, hP,
    ⟨hinWb, by rw [hTz1]; norm_num, hcne, hHCW, hμW, hNhaar⟩,
    (Classical.choice (hT t htt)).w, (Classical.choice (hT t htt)).w, ξ, 1, 1, hone, hone, ?_⟩
  intro h0
  rw [h0, inner_zero_right, hI] at h7
  have hfr : (Module.finrank ℂ Hπ : ℂ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Hπ)).ne'
  rcases mul_eq_zero.mp h7.symm with h | h
  · exact inv_ne_zero hfr h
  · exact hne h

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
