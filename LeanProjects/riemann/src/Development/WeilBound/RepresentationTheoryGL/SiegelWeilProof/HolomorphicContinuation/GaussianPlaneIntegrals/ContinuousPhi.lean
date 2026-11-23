import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

abbrev Sg (ι A B : Type) := (ι × A) ⊕ (ι × B)

def Phi (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Sg ι A B → ℂ :=
  Sum.elim (fun x => z (Sum.inl x)) (fun y => ∑ j, g y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g : Matrix ι ι ℂ) (f : PV ι A B) (z : Sg ι A B → ℂ) :
    eval z (sub 1 g f) = eval (Phi g z) f := by
  have h : (eval z).comp (sub (A := A) (B := B) 1 g).toRingHom = eval (Phi g z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [sub]
    · intro s
      rcases s with ⟨i, a⟩ | ⟨i, b⟩
      · simp [sub, Phi, Matrix.one_apply]
      · simp [sub, Phi]
  exact RingHom.congr_fun h f

theorem Phi_mul (g h : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : Phi (g * h) z = Phi g (Phi h z) := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp only [Phi, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

theorem Phi_one (z : Sg ι A B → ℂ) : Phi 1 z = z := by
  funext s
  rcases s with x | ⟨i, b⟩
  · rfl
  · simp [Phi, Matrix.one_apply]

theorem unitary_norm (U : Matrix ι ι ℂ) (hU : star U * U = 1) (v : ι → ℂ) :
    ∑ i, ‖∑ j, U i j * v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  apply Complex.ofReal_injective
  have key : star (U.mulVec v) ⬝ᵥ U.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU,
      Matrix.one_mulVec]
  have e1' : ∀ w : ι → ℂ, star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [← e1', ← e1', ← key]
  rfl

theorem norm_Phi (U : Matrix ι ι ℂ) (hU : star U * U = 1) (z : Sg ι A B → ℂ) :
    ∑ s, ‖Phi U z s‖ ^ 2 = ∑ s, ‖z s‖ ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact unitary_norm U hU fun j => z (Sum.inr (j, b))

def PhiL (g : Matrix ι ι ℂ) : (Sg ι A B → ℂ) →ₗ[ℝ] (Sg ι A B → ℂ) where
  toFun := Phi g
  map_add' z w := by
    funext s
    rcases s with x | y
    · rfl
    · simp [Phi, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext s
    rcases s with x | y
    · rfl
    · simp only [Phi, Sum.elim_inr, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.real_smul, Complex.real_smul]
      ring

theorem PhiL_apply (g : Matrix ι ι ℂ) (z : Sg ι A B → ℂ) : PhiL g z = Phi g z := rfl

theorem map_PhiL (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) :
    Measure.map (PhiL (A := A) (B := B) U) volume = volume := by
  set L := PhiL (A := A) (B := B) U
  set S : Set (Sg ι A B → ℂ) := {z | ∑ s, ‖z s‖ ^ 2 ≤ 1}
  have hU3 : star (star U) * star U = 1 := by rw [star_star]; exact hU2
  have himg : L '' S = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [S, Set.mem_setOf_eq, L, PhiL_apply, norm_Phi U hU1] at hw ⊢
      exact hw
    · intro hz
      refine ⟨Phi (star U) z, ?_, ?_⟩
      · simp only [S, Set.mem_setOf_eq, norm_Phi (star U) hU3]
        exact hz
      · simp only [L, PhiL_apply, ← Phi_mul, hU2, Phi_one]
  have hpos : 0 < volume S := by
    have hopen : IsOpen {z : Sg ι A B → ℂ | ∑ s, ‖z s‖ ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨0, by simp⟩) (measure_mono fun z hz => show ∑ s, ‖z s‖ ^ 2 ≤ 1 from le_of_lt hz)
  have hfin : volume S ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Sg ι A B → ℂ)) (r := 1)).ne
      (measure_mono fun z hz => ?_)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro s
    have h1 : ‖z s‖ ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (f := fun s => ‖z s‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ s)) hz
    nlinarith [norm_nonneg (z s)]
  have hdet : |LinearMap.det L| = 1 := by
    have h := Measure.addHaar_image_linearMap (volume : Measure (Sg ι A B → ℂ)) L S
    rw [himg] at h
    have h' : ENNReal.ofReal |LinearMap.det L| * volume S = 1 * volume S := by rw [← h, one_mul]
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h'
    exact (ENNReal.ofReal_eq_one).1 this
  have hne : LinearMap.det L ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact zero_ne_one hdet
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul]

theorem integral_Phi (U : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1)
    (H : (Sg ι A B → ℂ) → ℂ) (hH : Continuous H) :
    ∫ z, H z = ∫ z, H (Phi U z) := by
  have hL : Continuous (PhiL (A := A) (B := B) U) := LinearMap.continuous_of_finiteDimensional _
  conv_lhs => rw [← map_PhiL (A := A) (B := B) U hU1 hU2]
  rw [integral_map hL.measurable.aemeasurable hH.aestronglyMeasurable]
  rfl

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
