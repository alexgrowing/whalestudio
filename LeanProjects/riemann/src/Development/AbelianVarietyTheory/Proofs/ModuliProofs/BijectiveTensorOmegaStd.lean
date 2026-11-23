import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker

noncomputable section

namespace GlobalTheory.TensorSiegel

section General

variable {ι : Type*} [Fintype ι]

theorem re_realForm (M : Matrix ι ι ℝ) (z w : ι → ℂ) :
    (z ⬝ᵥ (M.map Complex.ofReal) *ᵥ star w).re =
      (fun i => (z i).re) ⬝ᵥ M *ᵥ (fun i => (w i).re) +
        (fun i => (z i).im) ⬝ᵥ M *ᵥ (fun i => (w i).im) := by
  simp [dotProduct, mulVec, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem im_realForm (M : Matrix ι ι ℝ) (z w : ι → ℂ) :
    (z ⬝ᵥ (M.map Complex.ofReal) *ᵥ star w).im =
      (fun i => (z i).im) ⬝ᵥ M *ᵥ (fun i => (w i).re) -
        (fun i => (z i).re) ⬝ᵥ M *ᵥ (fun i => (w i).im) := by
  simp [dotProduct, mulVec, Complex.re_sum, Complex.im_sum, Finset.sum_add_distrib]
  ring

theorem re_realForm_pos {M : Matrix ι ι ℝ} (hM : M.PosDef) {z : ι → ℂ} (hz : z ≠ 0) :
    0 < (z ⬝ᵥ (M.map Complex.ofReal) *ᵥ star z).re := by
  rw [re_realForm]
  have h1 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).re)
  have h2 := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).im)
  rw [star_trivial] at h1 h2
  by_cases hr : (fun i => (z i).re) = 0
  · have hi : (fun i => (z i).im) ≠ 0 := fun hi =>
      hz (funext fun i => Complex.ext (congrFun hr i) (congrFun hi i))
    have := hM.dotProduct_mulVec_pos hi
    rw [star_trivial] at this
    linarith
  · have := hM.dotProduct_mulVec_pos hr
    rw [star_trivial] at this
    linarith

theorem im_realForm_period (T : Matrix ι ι ℂ) (M N : Matrix ι ι ℝ)
    (h1 : (T.map Complex.im)ᵀ * M = N) (h2 : M * T.map Complex.im = N)
    (h3 : N * T.map Complex.re = (T.map Complex.re)ᵀ * N) (m n m' n' : ι → ℝ) :
    ((T *ᵥ ofRealVec m + ofRealVec n) ⬝ᵥ (M.map Complex.ofReal) *ᵥ
      star (T *ᵥ ofRealVec m' + ofRealVec n')).im = m ⬝ᵥ N *ᵥ n' - n ⬝ᵥ N *ᵥ m' := by
  have e : ∀ (A : Matrix ι ι ℝ) (a b : ι → ℝ), (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ Aᵀ *ᵥ b := fun A a b => by
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [im_realForm]
  simp only [im_mulVec_ofRealVec_add, re_mulVec_ofRealVec_add]
  rw [e, mulVec_mulVec, h1, mulVec_mulVec, h2, add_dotProduct, e, mulVec_add, dotProduct_add,
    mulVec_mulVec, mulVec_mulVec, h3]
  ring

theorem exists_posDef_smul_sub {G B : Matrix ι ι ℝ} (hG : G.PosDef) (hB : B.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • G - B).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hne : ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  have hc : ContinuousOn (fun x : ι → ℝ => (x ⬝ᵥ B *ᵥ x) / (x ⬝ᵥ G *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
      fun x hx => (hp x (hne x hx)).ne'
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  obtain ⟨κ₀, hκ₀⟩ := exists_nat_gt C
  refine ⟨κ₀, fun κ hκ => ?_⟩
  have hκ' : C < κ := hκ₀.trans_le (by exact_mod_cast hκ)
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine IsHermitian.sub ?_ hB
    rw [IsHermitian, conjTranspose_smul, hG.isHermitian.eq, star_trivial]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have h1 := hC ⟨_, hs, rfl⟩
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    rw [mul_div_mul_left _ _ (inv_pos.2 hn).ne', mul_div_mul_left _ _ (inv_pos.2 hn).ne',
      div_le_iff₀ (hp x hx)] at h1
    have h2 := mul_lt_mul_of_pos_right hκ' (hp x hx)
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith

end General

theorem re_hermForm_eq_of_span {g : ℕ} (H H' : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm H z w).im = (hermForm H' z w).im) (z w : Fin g → ℂ) :
    (hermForm H z w).re = (hermForm H' z w).re := by
  have h1 : ∀ z ∈ s, ∀ w, (hermForm H z w).im = (hermForm H' z w).im := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h z hz w hw
    | zero => simp [hermForm]
    | add w w' _ _ e e' =>
      simp only [hermForm, star_add, mulVec_add, dotProduct_add, Complex.add_im] at e e' ⊢
      rw [e, e']
    | smul c w _ e =>
      simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im] at e ⊢
      rw [e]
  have h2 : ∀ z w, (hermForm H z w).im = (hermForm H' z w).im := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact h1 z hz w
    | zero => simp [hermForm]
    | add z z' _ _ e e' =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at e e' ⊢
      rw [e, e']
    | smul c z _ e =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at e ⊢
      rw [e]
  have := h2 (Complex.I • z) w
  simpa [hermForm, smul_dotProduct] using this

section Kron

variable {r h g : ℕ} (σ : Fin r × Fin h ≃ Fin g) {R : Type*} [CommRing R]

def kron (S : Matrix (Fin r) (Fin r) R) (P : Matrix (Fin h) (Fin h) R) :
    Matrix (Fin g) (Fin g) R := (S ⊗ₖ P).submatrix σ.symm σ.symm

theorem kron_mul (S S' : Matrix (Fin r) (Fin r) R) (P P' : Matrix (Fin h) (Fin h) R) :
    kron σ S P * kron σ S' P' = kron σ (S * S') (P * P') := by
  rw [kron, kron, kron, submatrix_mul_equiv, mul_kronecker_mul]

theorem kron_transpose (S : Matrix (Fin r) (Fin r) R) (P : Matrix (Fin h) (Fin h) R) :
    (kron σ S P)ᵀ = kron σ Sᵀ Pᵀ := by
  ext i j; simp [kron]

theorem kron_mulVec (S : Matrix (Fin r) (Fin r) R) (P : Matrix (Fin h) (Fin h) R)
    (z : Fin g → R) (u : Fin r) (i : Fin h) :
    (kron σ S P *ᵥ z) (σ (u, i)) = ∑ v, S u v * ∑ j, P i j * z (σ (v, j)) := by
  simp only [mulVec, dotProduct]
  rw [← σ.sum_comp]
  simp [kron, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem kron_one_mulVec (P : Matrix (Fin h) (Fin h) R) (z : Fin g → R) (u : Fin r) (i : Fin h) :
    (kron σ 1 P *ᵥ z) (σ (u, i)) = ∑ j, P i j * z (σ (u, j)) := by
  simp [kron_mulVec, one_apply]

theorem kron_mulVec_one (S : Matrix (Fin r) (Fin r) R) (z : Fin g → R) (u : Fin r) (i : Fin h) :
    (kron σ S 1 *ᵥ z) (σ (u, i)) = ∑ v, S u v * z (σ (v, i)) := by
  simp [kron_mulVec, one_apply]

theorem kron_posDef {S : Matrix (Fin r) (Fin r) ℝ} {P : Matrix (Fin h) (Fin h) ℝ} (hS : S.PosDef)
    (hP : P.PosDef) : (kron σ S P).PosDef :=
  (hS.kronecker hP).submatrix σ.symm.injective

theorem kron_one_map_im (τ : Matrix (Fin h) (Fin h) ℂ) :
    (kron σ 1 τ).map Complex.im = kron σ 1 (τ.map Complex.im) := by
  ext i j
  by_cases hij : (σ.symm i).1 = (σ.symm j).1 <;> simp [kron, one_apply, hij]

theorem kron_one_map_re (τ : Matrix (Fin h) (Fin h) ℂ) :
    (kron σ 1 τ).map Complex.re = kron σ 1 (τ.map Complex.re) := by
  ext i j
  by_cases hij : (σ.symm i).1 = (σ.symm j).1 <;> simp [kron, one_apply, hij]

def coordFst (x : Fin r → (Fin h ⊕ Fin h → ℤ)) : Fin g → ℤ :=
  fun k => x (σ.symm k).1 (.inl (σ.symm k).2)

def coordSnd (x : Fin r → (Fin h ⊕ Fin h → ℤ)) : Fin g → ℤ :=
  fun k => x (σ.symm k).1 (.inr (σ.symm k).2)

def period (τ : Matrix (Fin h) (Fin h) ℂ) : (Fin r → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun x => kron σ 1 τ *ᵥ ofIntVec (coordFst σ x) + ofIntVec (coordSnd σ x)) (by
    intro x y
    have e1 : coordFst σ (x + y) = coordFst σ x + coordFst σ y := rfl
    have e2 : coordSnd σ (x + y) = coordSnd σ x + coordSnd σ y := rfl
    simp only [e1, e2, ofIntVec_add, mulVec_add]
    abel)

theorem period_def (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin r → (Fin h ⊕ Fin h → ℤ)) :
    period σ τ x = kron σ 1 τ *ᵥ ofIntVec (coordFst σ x) + ofIntVec (coordSnd σ x) := rfl

theorem period_apply (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin r → (Fin h ⊕ Fin h → ℤ))
    (u : Fin r) (i : Fin h) :
    period σ τ x (σ (u, i)) = τ.mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ) := by
  rw [period_def, Pi.add_apply, kron_one_mulVec]
  simp [ofIntVec, coordFst, coordSnd, mulVec, dotProduct]

theorem eq_period {τ : Matrix (Fin h) (Fin h) ℂ}
    {Q : (Fin r → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)}
    (hQ : ∀ x u i, Q x (σ (u, i)) =
      τ.mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) : Q = period σ τ := by
  refine AddMonoidHom.ext fun x => funext fun k => ?_
  obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective k
  rw [hQ, period_apply]

theorem range_period (τ : Matrix (Fin h) (Fin h) ℂ) :
    (period σ τ).range = periodLattice (kron σ 1 τ) := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨n, n', rfl⟩
    refine ⟨fun u => Sum.elim (fun i => n (σ (u, i))) (fun i => n' (σ (u, i))), ?_⟩
    rw [period_def]
    congr 3
    · ext k; simp [coordFst]
    · ext k; simp [coordSnd]

theorem period_isLattice {τ : Matrix (Fin h) (Fin h) ℂ} (hτ : (τ.map Complex.im).PosDef) :
    Function.Injective (period σ τ) ∧ DiscreteTopology (period σ τ).range ∧
      Submodule.span ℝ (Set.range (period σ τ)) = ⊤ := by
  have hu : IsUnit ((kron σ 1 τ).map Complex.im).det := by
    rw [kron_one_map_im]
    exact (isUnit_iff_isUnit_det _).1 (kron_posDef σ PosDef.one hτ).isUnit
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := intVec_eq_zero_of_period_eq_zero hu _ _ hx
    ext u (i | i)
    · simpa [coordFst] using congrFun h1 (σ (u, i))
    · simpa [coordSnd] using congrFun h2 (σ (u, i))
  · rw [range_period]
    exact discreteTopology_periodLattice_of_isUnit hu
  · rw [← AddMonoidHom.coe_range, range_period]
    exact span_periodLattice_eq_top_of_isUnit hu

def formMatrix (S : Matrix (Fin r) (Fin r) ℝ) (τ : Matrix (Fin h) (Fin h) ℂ) :
    Matrix (Fin g) (Fin g) ℂ := (kron σ S (τ.map Complex.im)⁻¹).map Complex.ofReal

theorem formMatrix_pos {S : Matrix (Fin r) (Fin r) ℝ} {τ : Matrix (Fin h) (Fin h) ℂ}
    (hS : S.PosDef) (hτ : (τ.map Complex.im).PosDef) {z : Fin g → ℂ} (hz : z ≠ 0) :
    0 < (hermForm (formMatrix σ S τ) z z).re :=
  re_realForm_pos (kron_posDef σ hS hτ.inv) hz

theorem formMatrix_isHermitian {S : Matrix (Fin r) (Fin r) ℝ} {τ : Matrix (Fin h) (Fin h) ℂ}
    (hS : S.PosDef) (hτ : (τ.map Complex.im).PosDef) : (formMatrix σ S τ).IsHermitian :=
  (kron_posDef σ hS hτ.inv).isHermitian.map _ (fun x => by simp)

theorem im_formMatrix_period (G : Matrix (Fin r) (Fin r) ℤ) {τ : Matrix (Fin h) (Fin h) ℂ}
    (hs : τ.IsSymm) (hτ : (τ.map Complex.im).PosDef) (x y : Fin r → (Fin h ⊕ Fin h → ℤ)) :
    (hermForm (formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ) (period σ τ x) (period σ τ y)).im =
      ((∑ u, ∑ v, G u v * omegaStd (x u) (y v) : ℤ) : ℝ) := by
  have hu : IsUnit (τ.map Complex.im).det := (isUnit_iff_isUnit_det _).1 hτ.isUnit
  have hY : (τ.map Complex.im)ᵀ = τ.map Complex.im := hs.map _
  have hX : (τ.map Complex.re)ᵀ = τ.map Complex.re := hs.map _
  rw [hermForm, formMatrix, period_def, period_def]
  simp only [ofIntVec_eq_ofRealVec]
  rw [im_realForm_period _ _ (kron σ (G.map (Int.cast : ℤ → ℝ)) 1)]
  · simp only [dotProduct]
    rw [← σ.sum_comp, ← σ.sum_comp]
    simp only [Fintype.sum_prod_type, kron_mulVec_one, coordFst, coordSnd, Equiv.symm_apply_apply,
      omegaStd, map_apply, ← Finset.sum_sub_distrib, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · rw [kron_one_map_im, kron_transpose, kron_mul, hY, mul_nonsing_inv _ hu, transpose_one,
      Matrix.one_mul]
  · rw [kron_one_map_im, kron_mul, nonsing_inv_mul _ hu, Matrix.mul_one]
  · rw [kron_one_map_re, kron_transpose, kron_mul, kron_mul, hX]
    simp

theorem eq_of_period_equiv [Nonempty (Fin r)] {τ τ' : Matrix (Fin h) (Fin h) ℂ}
    (e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ x, period σ τ' x = e (period σ τ x)) :
    τ = τ' := by
  have hb : ∀ (t : Matrix (Fin h) (Fin h) ℂ) (u : Fin r) (i : Fin h),
      period σ t (Pi.single u (Pi.single (.inr i) 1)) = Pi.single (σ (u, i)) 1 := by
    intro t u i
    ext k
    obtain ⟨⟨v, j⟩, rfl⟩ := σ.surjective k
    rw [period_apply]
    by_cases hv : v = u
    · subst hv
      simp [Pi.single_apply, mulVec, dotProduct]
    · simp [Pi.single_apply, mulVec, dotProduct, hv]
  have h1 : (e : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun k => ?_
    obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective k
    have := he (Pi.single u (Pi.single (.inr i) 1))
    rw [hb, hb] at this
    simpa using this.symm
  obtain ⟨u⟩ := ‹Nonempty (Fin r)›
  ext i j
  have h2 := he (Pi.single u (Pi.single (.inl j) 1))
  have h3 := LinearMap.congr_fun h1 (period σ τ (Pi.single u (Pi.single (.inl j) 1)))
  have h4 := congrFun (h2.trans h3) (σ (u, i))
  rw [LinearMap.id_apply, period_apply, period_apply] at h4
  simpa [Pi.single_apply, mulVec, dotProduct] using h4.symm

def endo (a : Matrix (Fin r) (Fin r) ℤ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ((kron σ (a.map (Int.cast : ℤ → ℝ)) 1).map Complex.ofReal).mulVecLin

theorem endo_period (a : Matrix (Fin r) (Fin r) ℤ) (τ : Matrix (Fin h) (Fin h) ℂ)
    (x : Fin r → (Fin h ⊕ Fin h → ℤ)) :
    endo σ a (period σ τ x) = period σ τ (fun u => ∑ v, a u v • x v) := by
  have e : (kron σ (a.map (Int.cast : ℤ → ℝ)) 1).map Complex.ofReal =
      kron σ (a.map (Int.cast : ℤ → ℂ)) 1 := by
    ext i j
    by_cases hij : (σ.symm i).2 = (σ.symm j).2 <;> simp [kron, one_apply, hij]
  ext k
  obtain ⟨⟨u, i⟩, rfl⟩ := σ.surjective k
  rw [endo, mulVecLin_apply, e, kron_mulVec_one]
  simp only [period_apply, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  simp only [Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
  ring

theorem hermForm_endo (a : Matrix (Fin r) (Fin r) ℤ) (S : Matrix (Fin r) (Fin r) ℝ)
    (τ : Matrix (Fin h) (Fin h) ℂ) (y : Fin g → ℂ) :
    (hermForm (formMatrix σ S τ) (endo σ a y) (endo σ a y)) =
      hermForm (formMatrix σ ((a.map (Int.cast : ℤ → ℝ))ᵀ * S * a.map (Int.cast : ℤ → ℝ)) τ) y y := by
  have e : ∀ A : Matrix (Fin g) (Fin g) ℝ,
      star (A.map Complex.ofReal *ᵥ y) = A.map Complex.ofReal *ᵥ star y := by
    intro A
    ext i
    simp [mulVec, dotProduct]
  have e2 : ∀ A B : Matrix (Fin g) (Fin g) ℝ,
      A.map Complex.ofReal * B.map Complex.ofReal = (A * B).map Complex.ofReal := fun A B =>
    (Matrix.map_mul (f := Complex.ofRealHom)).symm
  rw [hermForm, hermForm, endo, mulVecLin_apply, e, ← vecMul_transpose, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← transpose_map, formMatrix, formMatrix, e2, e2, kron_transpose,
    kron_mul, kron_mul]
  simp

theorem hermForm_smul_sub (c : ℝ) (S S' : Matrix (Fin r) (Fin r) ℝ)
    (τ : Matrix (Fin h) (Fin h) ℂ) (y : Fin g → ℂ) :
    (hermForm (formMatrix σ (c • S - S') τ) y y).re =
      c * (hermForm (formMatrix σ S τ) y y).re - (hermForm (formMatrix σ S' τ) y y).re := by
  have e : formMatrix σ (c • S - S') τ = c • formMatrix σ S τ - formMatrix σ S' τ := by
    ext i j
    simp [formMatrix, kron]
    ring
  rw [e, hermForm, hermForm, hermForm, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
  simp

end Kron

theorem bijective_tensor_omegaStd {r h : ℕ} (G : Matrix (Fin r) (Fin r) ℤ) (hG : IsUnit G.det)
    (EF : LinearMap.BilinForm ℤ (Fin r → (Fin h ⊕ Fin h → ℤ)))
    (hE : ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v)) : Function.Bijective EF := by
  have hl : ∀ x v i, EF x (Pi.single v (Pi.single (.inl i) 1)) =
      -((fun u => x u (.inr i)) ᵥ* G) v := by
    intro x v i
    rw [hE]
    simp only [vecMul, dotProduct, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single v]
    · simp [omegaStd, Pi.single_apply, mul_comm]
    · intro w _ hw
      simp [omegaStd, hw]
    · simp
  have hr : ∀ x v i, EF x (Pi.single v (Pi.single (.inr i) 1)) =
      ((fun u => x u (.inl i)) ᵥ* G) v := by
    intro x v i
    rw [hE]
    simp only [vecMul, dotProduct]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single v]
    · simp [omegaStd, Pi.single_apply, mul_comm]
    · intro w _ hw
      simp [omegaStd, hw]
    · simp
  have hi : ∀ z : Fin r → ℤ, z ᵥ* G = 0 → z = 0 := fun z hz => by
    have := congrArg (· ᵥ* G⁻¹) hz
    simpa [vecMul_vecMul, mul_nonsing_inv _ hG] using this
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun φ => ?_⟩
  · ext u (i | i)
    · refine congrFun (hi (fun u => x u (.inl i)) (funext fun v => ?_)) u
      rw [← hr, hx]; rfl
    · refine congrFun (hi (fun u => x u (.inr i)) (funext fun v => ?_)) u
      have := hl x v i
      rw [hx] at this
      simpa using this.symm
  · refine ⟨fun u => Sum.elim
      (fun i => ((fun v => φ (Pi.single v (Pi.single (.inr i) 1))) ᵥ* G⁻¹) u)
      (fun i => ((fun v => -φ (Pi.single v (Pi.single (.inl i) 1))) ᵥ* G⁻¹) u), ?_⟩
    refine LinearMap.pi_ext' fun v => LinearMap.pi_ext' fun c => LinearMap.ext_ring ?_
    rcases c with i | i
    · simp [hl, vecMul_vecMul, nonsing_inv_mul _ hG]
    · simp [hr, vecMul_vecMul, nonsing_inv_mul _ hG]

end GlobalTheory.TensorSiegel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TensorSiegel

theorem tensor_siegel_lattices : ∀ (h g : ℕ) (G : Matrix (Fin 8) (Fin 8) ℤ) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), G.IsSymm → (G.map (Int.cast : ℤ → ℝ)).PosDef → G.det = 1 → (∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v)) → Function.Bijective EF ∧ (∀ τ : Matrix (Fin h) (Fin h) ℂ, (τ).IsSymm ∧ ((τ).map Complex.im).PosDef → ∃ (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y)) ∧ (∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (Q Q' : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)), (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (∀ x u i, Q' x (σ (u, i)) = (τ').mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q' x = e (Q x)) → τ = τ') ∧ ∀ a : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ∀ (τ : Matrix (Fin h) (Fin h) ℂ) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (τ).IsSymm ∧ ((τ).map Complex.im).PosDef → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (fun u => ∑ v, a u v • x v)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro h g G σ EF _ hG hdet hE
  refine ⟨bijective_tensor_omegaStd G (by rw [hdet]; exact isUnit_one) EF hE, ?_, ?_, ?_⟩
  · rintro τ ⟨hs, hτ⟩
    obtain ⟨h1, h2, h3⟩ := period_isLattice σ hτ
    refine ⟨period σ τ, formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ, period_apply σ τ, h1, h2, h3,
      formMatrix_isHermitian σ hG hτ, fun z hz => formMatrix_pos σ hG hτ hz, fun x y => ?_⟩
    rw [im_formMatrix_period σ G hs hτ, hE]
  · rintro τ τ' Q Q' hQ hQ' ⟨e, he⟩
    rw [eq_period σ hQ, eq_period σ hQ'] at he
    exact eq_of_period_equiv σ e he
  · intro a
    have hB : ((a.map (Int.cast : ℤ → ℝ))ᵀ * G.map (Int.cast : ℤ → ℝ) *
        a.map (Int.cast : ℤ → ℝ)).IsHermitian := by
      have := Matrix.isHermitian_conjTranspose_mul_mul (a.map (Int.cast : ℤ → ℝ)) hG.isHermitian
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    obtain ⟨κ₀, hκ₀⟩ := exists_posDef_smul_sub hG hB
    refine ⟨κ₀, fun κ hκ τ Q Hm ⟨hs, hτ⟩ hQ ⟨_, _, h3, _, _, h6⟩ => ?_⟩
    obtain rfl := eq_period σ hQ
    refine ⟨endo σ a, endo_period σ a τ, fun y hy => ?_⟩
    have key := re_hermForm_eq_of_span Hm (formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ) _ h3 (by
      rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
      rw [h6, im_formMatrix_period σ G hs hτ, hE])
    have h7 := formMatrix_pos σ (hκ₀ κ hκ) hτ hy
    rw [hermForm_smul_sub] at h7
    rw [key, key, hermForm_endo]
    linarith

end GlobalTheory.TensorSiegel
