import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HaarDisintegrationReal : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc → DisintegrationConstantPositive X u u' sc

def StepReal : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∃ γ, HasDiag X u u' sc c γ

def StepInt : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StepEnergy : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    DisintegrationConstantPositive X u u' sc → CoordOK X u u' sc → intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X)

def StepDiagDC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ),
    ∀ c ∈ Good X u u', ∀ γ γ', HasDiag X u u' sc c γ → HasDiag X u u' sc c γ' →
      ∃ s ∈ X.SinfU u, ∃ s' ∈ X.SinfU u', γ' = s * γ * s'⁻¹

def StepPtRep : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k, PtRepExists X u u' sc i0 i0

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem rank_one_smul_isometry (a b : ℂ) (A : V ≃ₗᵢ[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') (v : V) (w : V') :
    TermOp.rk1 (a • A v) (b • B w) =
      (a * conj b) • ((A.toContinuousLinearEquiv : V →L[ℂ] V).comp
        ((TermOp.rk1 v w).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))) := by

  ext x
  have key : ⟪B w, x⟫_ℂ = ⟪w, B.symm x⟫_ℂ := by
    rw [← B.inner_map_map w (B.symm x), LinearIsometryEquiv.apply_symm_apply]
  simp [TermOp.rk1, inner_smul_left, smul_smul, key, map_smul]
  try ring_nf

theorem OO_equiv {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [CompleteSpace V] [CompleteSpace V'] (Ph : G → V) (Ph' : G → V') (γ s s' : G) (a b : ℂ)
    (A : V ≃ₗᵢ[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') (hA : ∀ x, Ph (s * x) = a • A (Ph x))
    (hB : ∀ x, Ph' (s' * x) = b • B (Ph' x)) :
    TermOp.OO μ Set.univ Ph Ph' (s * γ * s'⁻¹) =
      (a * conj b) • ((A.toContinuousLinearEquiv : V →L[ℂ] V).comp
        ((TermOp.OO μ Set.univ Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))) := by

  unfold TermOp.OO
  rw [Measure.restrict_univ]
  rw [← integral_mul_left_eq_self (fun x => TermOp.rk1 (Ph x) (Ph' ((s * γ * s'⁻¹)⁻¹ * x))) s]
  have e : ∀ y, TermOp.rk1 (Ph (s * y)) (Ph' ((s * γ * s'⁻¹)⁻¹ * (s * y))) =
      (a * conj b) • (ContinuousLinearEquiv.arrowCongr B.toContinuousLinearEquiv A.toContinuousLinearEquiv
        (TermOp.rk1 (Ph y) (Ph' (γ⁻¹ * y)))) := by
    intro y
    have hy : (s * γ * s'⁻¹)⁻¹ * (s * y) = s' * (γ⁻¹ * y) := by group
    rw [hy, hA, hB, rank_one_smul_isometry]
    congr 1
  simp only [e]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  try (ext x; simp [ContinuousLinearEquiv.arrowCongr_apply])

private theorem norm_sq_eq_sum_norm_inner_sq_orthonormalBasis {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ W) (x : W) : ‖x‖ ^ 2 = ∑ i, ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
  first
  | exact (b.sum_sq_norm_inner_right x).symm
  | exact (b.sum_sq_norm_inner_left x).symm
  | (rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]; simp [b.repr_apply_apply])

theorem hsb_eq_adj [FiniteDimensional ℂ V] [CompleteSpace V] [CompleteSpace V'] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ V') (A : V' →L[ℂ] V) :
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ k, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V k)‖ ^ 2 := by

  calc ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ∑ k, ‖⟪(stdOrthonormalBasis ℂ V k), A (b i)⟫_ℂ‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => norm_sq_eq_sum_norm_inner_sq_orthonormalBasis (stdOrthonormalBasis ℂ V) _
    _ = ∑ k, ∑ i, ‖⟪(stdOrthonormalBasis ℂ V k), A (b i)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ = ∑ k, ∑ i, ‖⟪b i, (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V k)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑ k, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V k)‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => (norm_sq_eq_sum_norm_inner_sq_orthonormalBasis b _).symm

theorem hsb_indep [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ V') (c : OrthonormalBasis κ ℂ V') (A : V' →L[ℂ] V) :
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ j, ‖A (c j)‖ ^ 2 := by

  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  haveI : CompleteSpace V' := FiniteDimensional.complete ℂ V'
  rw [hsb_eq_adj b A, hsb_eq_adj c A]

theorem hilbert_schmidt_comp_left [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) (T : V →L[ℂ] V) (hT : ∀ x, ‖T x‖ = ‖x‖) :
    hs2 (T.comp A) = hs2 A := by

  simp only [hs2, ContinuousLinearMap.comp_apply, hT]

theorem hilbert_schmidt_comp_right [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') :
    hs2 (A.comp (B.toContinuousLinearEquiv : V' →L[ℂ] V')) = hs2 A := by

  unfold hs2
  have h := hsb_indep ((stdOrthonormalBasis ℂ V').map B) (stdOrthonormalBasis ℂ V') A
  simp only [OrthonormalBasis.map_apply] at h
  simpa using h

theorem hilbert_schmidt_smul [FiniteDimensional ℂ V'] (c : ℂ) (A : V' →L[ℂ] V) : hs2 (c • A) = ‖c‖ ^ 2 * hs2 A := by

  simp only [hs2, ContinuousLinearMap.smul_apply, norm_smul, mul_pow, Finset.mul_sum]

end Gen

section Conc

open Formalism.L2.SG.HidaSetting

theorem inS_inv {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g gi : Matrix (Fin n) (Fin n) ℂ)
    (h1 : gi * g = 1) (hg : InS e z g) : InS e z gi := by
  have pres : ∀ a : ℕ, ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
    intro a y hy
    have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
      unfold spanLt
      rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : (b : ℕ) < a := hb
      simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      have e1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [e1]
      refine Submodule.add_mem _ (Submodule.subset_span ⟨b, hb', rfl⟩) ?_
      refine Submodule.span_mono ?_ (hg.1 b)
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, lt_trans hc hb', rfl⟩
    exact hle hy
  have ginj : Function.Injective (Matrix.mulVecLin g) := by
    intro x y hxy
    have := congrArg (fun t => gi *ᵥ t) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1] using this
  have ipres : ∀ a : ℕ, ∀ y ∈ spanLt e a, gi *ᵥ y ∈ spanLt e a := by
    intro a y hy
    have hle : (spanLt e a).map (Matrix.mulVecLin g) ≤ spanLt e a := by
      rintro _ ⟨x, hx, rfl⟩
      exact pres a x hx
    have heq : (spanLt e a).map (Matrix.mulVecLin g) = spanLt e a :=
      Submodule.eq_of_le_of_finrank_eq hle
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ ginj (spanLt e a))).symm
    rw [← heq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1] using hx
  have key : ∀ y : Fin n → ℂ, (gi - 1) *ᵥ y = -(gi *ᵥ ((g - 1) *ᵥ y)) := fun y => by
    simp [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]; exact Submodule.neg_mem _ (ipres a.1 _ (hg.1 a))
  · rw [key]; exact Submodule.neg_mem _ (ipres r _ hg.2)

theorem uMat_inv_mul' {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  simp [uMat]

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem sinfU_inv (u : D.what₂.Word) {s : X.B.I.Ginf} (hs : s ∈ X.SinfU u) : s⁻¹ ∈ X.SinfU u := by
  intro v
  exact inS_inv _ _ (uMat (s v)) (uMat (s⁻¹ v)) (uMat_inv_mul' (s v)) (hs v)

theorem hsetU_sub (u : D.what₂.Word) {h : X.B.I.Ginf} (hh : h ∈ HsetU X u) : h ∈ X.SinfU u := by
  intro v
  refine ⟨fun a => ?_, ?_⟩
  · have hv : uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      hh v _ (Or.inl (Or.inl ⟨a, rfl⟩))
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact (sub_eq_zero.mpr hv) ▸ Submodule.zero_mem _
  · have hv : uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) := hh v _ (Or.inr rfl)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact (sub_eq_zero.mpr hv) ▸ Submodule.zero_mem _

theorem hsetU_inv (u : D.what₂.Word) {h : X.B.I.Ginf} (hh : h ∈ HsetU X u) : h⁻¹ ∈ HsetU X u := by
  intro v x hx
  have hv := hh v x hx
  calc uMat (h⁻¹ v) *ᵥ rv X.B.I v x = uMat (h⁻¹ v) *ᵥ (uMat (h v) *ᵥ rv X.B.I v x) := by rw [hv]
    _ = rv X.B.I v x := by
      rw [Matrix.mulVec_mulVec, show uMat (h⁻¹ v) * uMat (h v) = 1 from uMat_inv_mul' (h v), Matrix.one_mulVec]

def piIso (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u :=
  ((X.piU u s).toLinearMap.isometryOfInner (fun x y => (X.piU_rep u).2.2.1 s hs x y)).toLinearIsometryEquiv rfl

theorem piIso_apply (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) (x : X.Vpi u) :
    piIso X u s hs x = X.piU u s x := rfl

theorem piIso_coe (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) :
    ((piIso X u s hs).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u) = X.piU u s := by

  ext x
  exact piIso_apply X u s hs x

theorem piIso_symm (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) :
    ((piIso X u s hs).symm.toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u) = X.piU u s⁻¹ := by
  ext x
  show (piIso X u s hs).symm x = X.piU u s⁻¹ x
  rw [LinearIsometryEquiv.symm_apply_eq, piIso_apply, ← ContinuousLinearMap.mul_apply,
    ← (X.piU_rep u).2.1 s hs s⁻¹ (sinfU_inv X u hs), mul_inv_cancel, (X.piU_rep u).1,
    ContinuousLinearMap.one_apply]

theorem norm_psiR {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by

  unfold psiR
  have hS : ∀ x : ℂ, x + star x = ((2 * x.re : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, Complex.add_conj]
    try push_cast
    try ring
  simp only [hS]
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.div_re, Complex.div_im]

theorem norm_psiInfU (u : D.what₂.Word) (s : X.B.I.Ginf) : ‖X.psiInfU u s‖ = 1 := by
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.psiInfU psiInf
  rw [norm_prod]
  exact Finset.prod_eq_one fun v _ => norm_psiR _ _ _ _ _ _

theorem ooEquivar (u u' : D.what₂.Word) : OOEquivar X u u' := by
  intro γ s hs s' hs'
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI := FiniteDimensional.complete ℂ (X.Vpi u')
  have hA : ∀ x, X.Wu u (s * x) = X.psiInfU u s • piIso X u s hs (X.Wu u x) :=
    fun x => (X.Wu_spec u).1 s hs x
  have hB : ∀ x, X.Wu u' (s' * x) = X.psiInfU u' s' • piIso X u' s' hs' (X.Wu u' x) :=
    fun x => (X.Wu_spec u').1 s' hs' x
  unfold OOinf
  rw [OO_equiv _ _ _ γ s s' _ _ (piIso X u s hs) (piIso X u' s' hs') hA hB, piIso_symm, piIso_coe]

theorem hilbert_schmidt_unitary_conj (u u' : D.what₂.Word) (A : X.Vpi u' →L[ℂ] X.Vpi u) (s s' : X.B.I.Ginf)
    (hs : s ∈ X.SinfU u) (hs' : s' ∈ X.SinfU u') (c : ℂ) (hc : ‖c‖ = 1) :
    hs2 (c • ((X.piU u s).comp (A.comp (X.piU u' s'⁻¹)))) = hs2 A := by

  have hs'i := sinfU_inv X u' hs'
  have hT : ∀ x, ‖X.piU u s x‖ = ‖x‖ := fun x => by
    rw [← piIso_apply X u s hs x]
    exact (piIso X u s hs).norm_map x
  rw [hilbert_schmidt_smul, hc, one_pow, one_mul, hilbert_schmidt_comp_left _ _ hT, ← piIso_coe X u' s'⁻¹ hs'i, hilbert_schmidt_comp_right]

theorem ooIndep_of_step (hDC : StepDiagDC) (u u' : D.what₂.Word) (sc : ℝ) : OOIndep X u u' sc := by
  intro c hc γ γ' h1 h2
  obtain ⟨s, hs, s', hs', rfl⟩ := hDC D X u u' sc c hc γ γ' h1 h2
  rw [ooEquivar X u u' γ s hs s' hs', hilbert_schmidt_unitary_conj X u u' _ s s' hs hs']
  rw [norm_mul, Complex.norm_conj, norm_psiInfU, norm_psiInfU, one_mul]

theorem dl_cont {r : ℕ} (l : ℕ) : Continuous (fun Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ => Dl Z l) := by

  unfold Dl
  by_cases h : l ≤ r + 1
  · simp only [h, dif_pos]
    first
    | exact (continuous_id.matrix_submatrix _ _).matrix_det
    | fun_prop
  · simp only [h, dif_neg, not_false_eq_true]
    exact continuous_const

theorem wt_cont (u u' : D.what₂.Word) : Continuous (wt X u u') := by
  unfold wt
  refine continuous_finset_prod _ fun v _ => ?_
  have hd : Continuous (fun c : Cinf X => Matrix.diagonal (c v)) := (continuous_apply v).matrix_diagonal
  have hD : ∀ l, Continuous (fun c : Cinf X => Dl (Matrix.diagonal (c v)) l) := fun l => (dl_cont l).comp hd
  refine Continuous.mul ?_ ?_
  · unfold Gv
    exact ((((hD _).norm.pow 2).sub (continuous_const.mul ((hD _).norm.pow 2)))).pow _
  · unfold JacV modC
    exact continuous_finset_prod _ fun l _ => ((hD l).norm.pow 2).pow 2

theorem inNuX (u u' : D.what₂.Word) (sc : ℝ) : InNuX X u u' sc :=
  inNuX_of_meas X u u' sc (wt_cont X u u').measurable

end Conc

end Formalism.L2.SG.RealObj.InfCut
