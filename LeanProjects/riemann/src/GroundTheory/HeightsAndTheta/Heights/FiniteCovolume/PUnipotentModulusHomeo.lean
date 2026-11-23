import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusCoords

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem continuous_hForm_self (H : Matrix ι ι ℂ) {X : Type*} [TopologicalSpace X] {y : X → ι → ℂ}
    (hy : Continuous y) : Continuous fun x => hForm H (y x) (y x) :=
  (continuous_star.comp hy).dotProduct (continuous_const.matrix_mulVec hy)

omit [DecidableEq ι] in
theorem continuous_hForm_right (H : Matrix ι ι ℂ) (u : ι → ℂ) {X : Type*} [TopologicalSpace X]
    {y : X → ι → ℂ} (hy : Continuous y) : Continuous fun x => hForm H u (y x) :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec hy)

omit [DecidableEq ι] in
theorem heisS_eq (H : Matrix ι ι ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H y t = ((-(hForm H y y).re / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [heisS]

theorem continuous_heisMat_heisS (H : Matrix ι ι ℂ) (a : ι → ℂ) {X : Type*} [TopologicalSpace X]
    {y : X → ι → ℂ} {t : X → ℝ} (hy : Continuous y) (ht : Continuous t) :
    Continuous fun x => heisMat H a (y x) (heisS H (y x) (t x)) := by
  have hs : Continuous fun x => heisS H (y x) (t x) := by
    simp only [heisS_eq]
    exact (Complex.continuous_ofReal.comp
      ((Complex.continuous_re.comp (continuous_hForm_self H hy)).neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp ht).mul continuous_const)
  unfold heisMat
  exact (continuous_const.add ((hy.add (hs.smul continuous_const)).matrix_vecMulVec
    continuous_const)).sub (continuous_const.matrix_vecMulVec
      ((continuous_star.comp hy).matrix_vecMul continuous_const))

section Homeo

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in
theorem continuous_unipRadical_at (w : InfinitePlace E) :
    Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
  Units.continuous_val.comp ((continuous_apply w).comp
    (continuous_subtype_val.comp continuous_subtype_val))

theorem heisU_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    heisU (w₀ := w₀) (heisPoint hp p) w = (p.1 : InfinitePlace E → ι → ℂ) w +
      heisS (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (p.2 w) • vecAt v x₀ w := by
  obtain ⟨hH, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
  have hyb : hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
    rw [← hForm_conj hH, (p.1.2 w).2, map_zero]
  rw [heisU, heisPoint_val, heisMatAt, heisMat_mulVec, hab, hyb]
  simp only [one_smul, zero_smul, sub_zero, add_sub_cancel_left]

theorem hForm_heisU_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) (heisPoint hp p) w) =
      heisS (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w) (p.2 w) := by
  obtain ⟨hH, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
  have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hab, map_one]
  rw [heisU_heisPoint, hForm_add_right, hForm_smul_right, (p.1.2 w).2, hba]
  ring

theorem heisCoordOf_heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisCoordOf hp (heisPoint hp p) = p := by
  refine Prod.ext (Subtype.ext (funext fun w => ?_)) (funext fun w => ?_)
  · change heisYOf (w₀ := w₀) (heisPoint hp p) w = (p.1 : InfinitePlace E → ι → ℂ) w
    rw [heisYOf, hForm_heisU_heisPoint, heisU_heisPoint, add_sub_cancel_right]
  · change (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) (heisPoint hp p) w)).im = p.2 w
    rw [hForm_heisU_heisPoint, heisS_im]

theorem heisPoint_heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) :
    heisPoint hp (heisCoordOf hp n) = n := by
  apply Subtype.ext
  apply Subtype.ext
  funext w
  apply Units.ext
  obtain ⟨-, -, h3, h4⟩ := heisYOf_spec hp n w
  rw [heisPoint_val]
  conv_rhs => rw [h4]
  exact congrArg (heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w))
    (eq_heisS h3).symm

def heisHomeo (hp : IsHyperbolicPair h x₀ w₀) : HeisCoord h v x₀ w₀ ≃ₜ unipRadical h v x₀ where
  toFun := heisPoint hp
  invFun := heisCoordOf hp
  left_inv := heisCoordOf_heisPoint hp
  right_inv := heisPoint_heisCoordOf hp
  continuous_toFun := by
    have hy : Continuous fun p : HeisCoord h v x₀ w₀ => (p.1 : InfinitePlace E → ι → ℂ) :=
      continuous_subtype_val.comp continuous_fst
    have ht : Continuous fun p : HeisCoord h v x₀ w₀ => p.2 := continuous_snd
    refine continuous_induced_rng.2 (continuous_induced_rng.2 (continuous_pi fun w => ?_))
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_heisMat_heisS _ _ ((continuous_apply w).comp hy)
        ((continuous_apply w).comp ht)
    · exact continuous_heisMat_heisS _ _ ((continuous_apply w).comp hy.neg)
        ((continuous_apply w).comp ht.neg)
  continuous_invFun := by
    have hu : ∀ w, Continuous fun n : unipRadical h v x₀ => heisU (w₀ := w₀) n w := fun w =>
      ((continuous_unipRadical_at w).matrix_mulVec continuous_const).sub continuous_const
    have hs : ∀ w, Continuous fun n : unipRadical h v x₀ =>
        hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) := fun w =>
      continuous_hForm_right _ _ (hu w)
    refine Continuous.prodMk (f := fun n => (heisCoordOf hp n).1)
      (g := fun n => (heisCoordOf hp n).2) ?_ ?_
    · refine continuous_induced_rng.2 (continuous_pi fun w => ?_)
      exact (hu w).sub ((hs w).smul continuous_const)
    · exact continuous_pi fun w => Complex.continuous_im.comp (hs w)

theorem heisHomeo_apply (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisHomeo hp p = heisPoint hp p := rfl

theorem heisPoint_mul (hp : IsHyperbolicPair h x₀ w₀) (p q : HeisCoord h v x₀ w₀) :
    heisPoint hp p * heisPoint hp q = heisPoint hp (p.1 + q.1, p.2 + q.2 - fun w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((q.1 : InfinitePlace E → ι → ℂ) w)).im) := by
  apply Subtype.ext
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisPoint_val, heisMatAt_mul hp p.1.2 q.1.2]
  rfl

def heisConjLin (g : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) :
    heisY h v x₀ w₀ →ₗ[ℝ] heisY h v x₀ w₀ where
  toFun y := ⟨fun w => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
      (y : InfinitePlace E → ι → ℂ) w, fun w => by
    have ha := (Subgroup.mem_inf.1 hg).1 w
    have hb := (Subgroup.mem_inf.1 hg).2 w
    constructor
    · conv_lhs => rw [← ha]
      rw [hForm_mulVec_of_unitary _ (archUnitary_at_place g w), (y.2 w).1]
    · conv_lhs => rw [← hb]
      rw [hForm_mulVec_of_unitary _ (archUnitary_at_place g w), (y.2 w).2]⟩
  map_add' y z := by
    apply Subtype.ext
    funext w
    simp [mulVec_add]
  map_smul' c y := by
    apply Subtype.ext
    funext w
    change _ *ᵥ (c • (y : InfinitePlace E → ι → ℂ) w) =
      c • (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w)
    rw [real_smul_vec, real_smul_vec, mulVec_smul]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in
theorem heisConjLin_apply (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y : heisY h v x₀ w₀) (w : InfinitePlace E) :
    ((heisConjLin g hg y : heisY h v x₀ w₀) : InfinitePlace E → ι → ℂ) w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w := rfl

theorem heisPoint_conj (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisConjLin g hg p.1, p.2) := by
  apply Subtype.ext
  funext w
  apply Units.ext
  have ha := (Subgroup.mem_inf.1 hg).1 w
  have hu := archUnitary_at_place g w
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisMatAt, heisMatAt, heisMat_conj hu ha, mul_assoc,
    Units.mul_inv, mul_one, heisConjLin_apply]
  congr 1
  simp only [heisS, hForm_mulVec_of_unitary _ hu]

end Homeo

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
