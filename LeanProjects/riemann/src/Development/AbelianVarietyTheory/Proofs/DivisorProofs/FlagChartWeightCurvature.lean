import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.VertChart

variable {n : ℕ}

abbrev Up (M : Matrix (Fin n) (Fin n) ℂ) : Prop := M.BlockTriangular id

theorem up_inv {T : Matrix (Fin n) (Fin n) ℂ} (hT : Up T) (hu : IsUnit T.det) : Up T⁻¹ := by
  letI := invertibleOfIsUnitDet T hu
  exact blockTriangular_inv_of_blockTriangular hT

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι]

theorem mdel_zero_vec {m k : Type*} (A : E → Matrix m k ℂ) (z : E) : mdel A z 0 = 0 := by
  simpa using mdel_smul_vec A z 0 0

theorem theta_vert (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (y ξ : E) (h : fderiv ℂ π y ξ = 0) :
    thetaOneZero H π e y ξ = (e y)⁻¹ * mdel e y ξ := by
  have : conn H (π y) 0 = 0 := by simp [conn, mdel_zero_vec]
  simp [thetaOneZero, h, this]

theorem diagVal_vertForm (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (y ξ : E) :
    diagVal (vertForm H π e lam y) ξ =
      (∑ i, ∑ l ∈ Finset.Ioi i, (lam i - lam l) * normSq (thetaOneZero H π e y ξ l i)) /
        (2 * Real.pi) := by
  set r := ∑ i, ∑ l ∈ Finset.Ioi i, (lam i - lam l) * normSq (thetaOneZero H π e y ξ l i)
  have h : vertForm H π e lam y ξ ξ = kappa * (r : ℂ) := by
    simp only [vertForm, thetaSq, mul_conj, r, ofReal_sum, ofReal_mul]
  rw [diagVal, h, kappa]
  have : -I * (I / (2 * (Real.pi : ℂ)) * (r : ℂ)) = ((r / (2 * Real.pi) : ℝ) : ℂ) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    rw [I_sq]; ring
  rw [this, ofReal_re]

section Main

variable {n : ℕ} {U : Set (ι → ℂ)} {H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ} {Y : Set E}
  {π : E → ι → ℂ} {A e : E → Matrix (Fin n) (Fin n) ℂ}

theorem e_isUnit (hE : IsUnitaryFlagFrame Y H π A e) {x : E} (hx : x ∈ Y) :
    IsUnit (e x).det := by
  have h1 : (e x)ᵀ * (H (π x) * (e x)ᴴᵀ) = 1 := by
    ext k l
    have := hE.unitary x hx k l
    rw [form_eq_sum] at this
    rw [one_apply, ← this]
    simp only [mul_apply, transpose_apply, conjTranspose_apply, star_def, Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have h2 := congrArg det h1
  rw [det_mul, det_one, det_transpose] at h2
  exact isUnit_iff_exists_inv.2 ⟨_, h2⟩

theorem T_up (hF : IsFlagFamily Y U π A) (hE : IsUnitaryFlagFrame Y H π A e) {x : E}
    (hx : x ∈ Y) : Up ((A x)⁻¹ * e x) := by
  intro a i hia
  have hmem := hE.mem x hx i
  have key : ∀ v ∈ Submodule.span ℂ {v : Fin n → ℂ | ∃ j ≤ i, v = fun a => A x a j},
      ((A x)⁻¹ *ᵥ v) a = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, hj, rfl⟩ := hv
      have hc : (fun a => A x a j) = A x *ᵥ Pi.single j 1 := by
        ext b; simp [mulVec, dotProduct, Pi.single_apply]
      rw [hc, mulVec_mulVec, nonsing_inv_mul _ (hF.isUnit x hx), one_mulVec]
      have : a ≠ j := fun h => by subst h; exact absurd (lt_of_le_of_lt hj hia) (lt_irrefl _)
      simp [Pi.single_apply, this]
    | zero => simp
    | add v w _ _ hv hw => simp [mulVec_add, hv, hw]
    | smul c v _ hv => simp [mulVec_smul, hv]
  have := key _ hmem
  simpa [mul_apply, mulVec, dotProduct] using this

theorem smooth_at (hF : IsFlagFamily Y U π A) (hE : IsUnitaryFlagFrame Y H π A e) {y : E}
    (hy : y ∈ Y) : MContDiffAt 1 A y ∧ MContDiffAt 1 e y := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · exact (((hF.hol_frame a b).contDiffAt (hF.isOpen.mem_nhds hy)).restrict_scalars ℝ).of_le
      (by norm_cast)
  · exact ((hE.smooth a b).contDiffAt (hF.isOpen.mem_nhds hy)).of_le (by norm_cast)

theorem theta_decomp (hF : IsFlagFamily Y U π A) (hE : IsUnitaryFlagFrame Y H π A e) {y ξ : E}
    (hy : y ∈ Y) (hv : fderiv ℂ π y ξ = 0) :
    thetaOneZero H π e y ξ = ((A y)⁻¹ * e y)⁻¹ * mdel (fun x => (A x)⁻¹ * e x) y ξ +
      ((A y)⁻¹ * e y)⁻¹ * flagDeriv A y ξ * ((A y)⁻¹ * e y) := by
  obtain ⟨hA, he⟩ := smooth_at hF hE hy
  have hAu := hF.isUnit y hy
  have hT : MContDiffAt 1 (fun x => (A x)⁻¹ * e x) y := (hA.inv hAu).mul he
  have heq : e =ᶠ[𝓝 y] fun x => A x * ((A x)⁻¹ * e x) :=
    Filter.mem_of_superset (hF.isOpen.mem_nhds hy) fun x hx =>
      (mul_nonsing_inv_cancel_left _ _ (hF.isUnit x hx)).symm
  have hm : mdel e y ξ = A y * mdel (fun x => (A x)⁻¹ * e x) y ξ +
      mdel A y ξ * ((A y)⁻¹ * e y) := by
    rw [mdel_congr heq, mdel_mul hA hT]
  have hey : e y = A y * ((A y)⁻¹ * e y) := (mul_nonsing_inv_cancel_left _ _ hAu).symm
  rw [theta_vert H π e y ξ hv, hm]
  conv_lhs => rw [hey]
  rw [Matrix.mul_inv_rev, Matrix.mul_add, flagDeriv]
  congr 1
  · rw [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hAu]
  · simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hAu]

theorem mdel_T_up (hF : IsFlagFamily Y U π A) (hE : IsUnitaryFlagFrame Y H π A e) {y : E}
    (hy : y ∈ Y) (ξ : E) : Up (mdel (fun x => (A x)⁻¹ * e x) y ξ) := by
  intro a b hab
  rw [mdel_apply, del_congr (g := fun _ => (0 : ℂ))]
  · simp
  · exact Filter.mem_of_superset (hF.isOpen.mem_nhds hy) fun x hx => T_up hF hE hx hab

end Main

theorem vert_chart_iff : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ)
    (U : Set (ι → ℂ)) (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e → ∀ y ∈ Y,
      ∀ lam : Fin n → ℝ, IsFlagChartAt π A y →
      ((∀ ξ, ξ ≠ 0 → fderiv ℂ π y ξ = 0 → 0 < diagVal (vertForm H π e lam y) ξ) ↔
        StrictAnti lam) := by
  intro E _ _ _ _ _ ι _ n U H Y π A e _ hF hE y hy lam hC
  set T := (A y)⁻¹ * e y with hTdef
  have hTu : IsUnit T.det := by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (hF.isUnit y hy)).mul (e_isUnit hE hy)
  have hTup : Up T := T_up hF hE hy
  have hTi : Up T⁻¹ := up_inv hTup hTu
  have hD : ∀ ξ, fderiv ℂ π y ξ = 0 →
      Up (thetaOneZero H π e y ξ - T⁻¹ * flagDeriv A y ξ * T) := by
    intro ξ hv
    rw [theta_decomp hF hE hy hv, add_sub_cancel_right]
    exact hTi.mul (mdel_T_up hF hE hy ξ)
  constructor
  · intro hP b a hba
    obtain ⟨ξ, hv, hξ⟩ := hC.2 0 (T * Matrix.single a b 1 * T⁻¹)
    have hFX : Up (flagDeriv A y ξ - T * Matrix.single a b 1 * T⁻¹) := by
      intro l i hil; rw [Matrix.sub_apply, hξ i l hil, sub_self]
    have hconj : T⁻¹ * (T * Matrix.single a b 1 * T⁻¹) * T = Matrix.single a b 1 := by
      simp only [Matrix.mul_assoc, nonsing_inv_mul _ hTu, Matrix.mul_one,
        nonsing_inv_mul_cancel_left _ _ hTu]
    have hup : Up (thetaOneZero H π e y ξ - Matrix.single a b 1) := by
      have h2 : Up (T⁻¹ * (flagDeriv A y ξ - T * Matrix.single a b 1 * T⁻¹) * T) :=
        (hTi.mul hFX).mul hTup
      rw [Matrix.mul_sub, Matrix.sub_mul, hconj] at h2
      have := (hD ξ hv).add h2
      rwa [sub_add_sub_cancel] at this
    have hθ : ∀ l i, i < l → thetaOneZero H π e y ξ l i = Matrix.single a b (1 : ℂ) l i := by
      intro l i hil
      have := hup hil
      rwa [Matrix.sub_apply, sub_eq_zero] at this
    have hξ0 : ξ ≠ 0 := by
      rintro rfl
      have := hθ a b hba
      simp [thetaOneZero, mdel_zero_vec, conn] at this
    have h := hP ξ hξ0 hv
    rw [diagVal_vertForm] at h
    have hS : (∑ i, ∑ l ∈ Finset.Ioi i, (lam i - lam l) *
        normSq (thetaOneZero H π e y ξ l i)) = lam b - lam a := by
      rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
      · rw [hθ a b hba]; simp
      · intro l hl hla; rw [hθ l b (Finset.mem_Ioi.1 hl)]; simp [Matrix.single_apply, Ne.symm hla]
      · intro h; exact absurd (Finset.mem_Ioi.2 hba) h
      · intro i _ hib
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [hθ l i (Finset.mem_Ioi.1 hl)]; simp [Matrix.single_apply, Ne.symm hib]
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hS] at h
    have hpi : 0 < 2 * Real.pi := by positivity
    have := (div_pos_iff_of_pos_right hpi).1 h
    linarith
  · intro hS ξ hξ0 hv
    rw [diagVal_vertForm]
    refine div_pos ?_ (by positivity)
    have hex : ∃ b a, b < a ∧ thetaOneZero H π e y ξ a b ≠ 0 := by
      by_contra hne
      push Not at hne
      have hθup : Up (thetaOneZero H π e y ξ) := fun a b hab => hne b a hab
      have hM : Up (T⁻¹ * flagDeriv A y ξ * T) := by
        have := hθup.sub (hD ξ hv); rwa [sub_sub_cancel] at this
      have hFup : Up (flagDeriv A y ξ) := by
        have := (hTup.mul hM).mul hTi
        rwa [show T * (T⁻¹ * flagDeriv A y ξ * T) * T⁻¹ = flagDeriv A y ξ by
          simp only [Matrix.mul_assoc, mul_nonsing_inv _ hTu, Matrix.mul_one,
            mul_nonsing_inv_cancel_left _ _ hTu]] at this
      exact hξ0 (hC.1 ξ hv fun i l hil => hFup hil)
    obtain ⟨b, a, hba, hne⟩ := hex
    apply Finset.sum_pos'
    · intro i _; apply Finset.sum_nonneg; intro l hl
      exact mul_nonneg (sub_nonneg.2 (hS (Finset.mem_Ioi.1 hl)).le) (normSq_nonneg _)
    · refine ⟨b, Finset.mem_univ _, Finset.sum_pos' ?_ ⟨a, Finset.mem_Ioi.2 hba, ?_⟩⟩
      · intro l hl; exact mul_nonneg (sub_nonneg.2 (hS (Finset.mem_Ioi.1 hl)).le) (normSq_nonneg _)
      · exact mul_pos (sub_pos.2 (hS hba)) (normSq_pos.2 hne)

end GlobalTheory.VertChart
