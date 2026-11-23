import Mathlib
import GroundTheory.HeightsAndTheta.Theta.RealSignature
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
import GroundTheory.AutomorphicForms.HermitianLocalForms

namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic NumberField NumberField.InfinitePlace.Completion TensorProduct

section QuadComplex

variable {R : Type*} [Field R] (φ : R ≃+* ℝ) {a : R} (ha : φ a < 0)

noncomputable def quadComplexEquiv : QuadraticAlgebra R a 0 ≃+* ℂ where
  toFun z := ⟨φ z.re, φ z.im * Real.sqrt (-φ a)⟩
  invFun c := ⟨φ.symm c.re, φ.symm (c.im / Real.sqrt (-φ a))⟩
  left_inv z := by
    have hs : Real.sqrt (-φ a) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 ha)).ne'
    ext
    · simp
    · simp [hs]
  right_inv c := by
    have hs : Real.sqrt (-φ a) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 ha)).ne'
    apply Complex.ext
    · simp
    · simp [hs]
  map_mul' z w := by
    have hsq : Real.sqrt (-φ a) * Real.sqrt (-φ a) = -φ a := Real.mul_self_sqrt (neg_pos.2 ha).le
    apply Complex.ext
    · simp only [QuadraticAlgebra.re_mul, map_add, map_mul, Complex.mul_re]
      linear_combination (φ z.im * φ w.im) * hsq
    · simp only [QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero,
        Complex.mul_im]
      ring
  map_add' z w := by
    apply Complex.ext
    · simp
    · simp [add_mul]

theorem quadComplexEquiv_apply (z : QuadraticAlgebra R a 0) :
    quadComplexEquiv φ ha z = ⟨φ z.re, φ z.im * Real.sqrt (-φ a)⟩ := rfl

theorem quadComplexEquiv_star (z : QuadraticAlgebra R a 0) :
    quadComplexEquiv φ ha (star z) = starRingEnd ℂ (quadComplexEquiv φ ha z) := by
  apply Complex.ext
  · simp [quadComplexEquiv_apply, QuadraticAlgebra.re_star]
  · simp [quadComplexEquiv_apply, QuadraticAlgebra.im_star]

theorem quadComplexEquiv_algebraMap (r : R) :
    quadComplexEquiv φ ha (algebraMap R (QuadraticAlgebra R a 0) r) = (φ r : ℂ) := by
  apply Complex.ext <;> simp [quadComplexEquiv_apply, QuadraticAlgebra.algebraMap_eq]

end QuadComplex

section Place

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]

theorem two_ne_zero_of_infinitePlace (w : InfinitePlace K) : (2 : K) ≠ 0 := by
  intro h
  have := congrArg w.embedding h
  rw [map_ofNat, map_zero] at this
  exact two_ne_zero this

omit [Algebra.IsQuadraticExtension K E] in
variable (E) in

def IsNonsplitAt (w : InfinitePlace K) : Prop := IsField (w.Completion ⊗[K] E)

variable (K E) in

noncomputable def quadD (w : InfinitePlace K) : K :=
  (exists_algEquiv_quadraticAlgebra K E (two_ne_zero_of_infinitePlace w)).choose

variable (K E) in

noncomputable def quadPsi (w : InfinitePlace K) : E ≃ₐ[K] QuadraticAlgebra K (quadD K E w) 0 :=
  (exists_algEquiv_quadraticAlgebra K E (two_ne_zero_of_infinitePlace w)).choose_spec.choose

theorem quadPsi_conj (w : InfinitePlace K) (x : E) :
    quadPsi K E w (conj K E x) = star (quadPsi K E w x) :=
  (exists_algEquiv_quadraticAlgebra K E (two_ne_zero_of_infinitePlace w)).choose_spec.choose_spec.2 x

variable {w : InfinitePlace K} (hw : w.IsReal)

noncomputable def realPlaceD : ℝ :=
  ringEquivRealOfIsReal hw (algebraMap K w.Completion (quadD K E w))

noncomputable def realPlaceTensorEquiv :
    w.Completion ⊗[K] E ≃ₐ[w.Completion]
      QuadraticAlgebra w.Completion (algebraMap K w.Completion (quadD K E w)) 0 :=
  tensorQuadEquiv (quadPsi K E w) w.Completion

theorem realPlaceD_neg (hE : IsNonsplitAt E w) : realPlaceD (E := E) hw < 0 := by
  set φ := ringEquivRealOfIsReal hw
  set dw := algebraMap K w.Completion (quadD K E w)
  have hF : IsField (QuadraticAlgebra w.Completion dw 0) :=
    MulEquiv.isField hE (realPlaceTensorEquiv (E := E) (w := w)).symm.toMulEquiv
  by_contra hnn
  push Not at hnn
  set r := φ.symm (Real.sqrt (φ dw))
  have hr : r * r = dw := by
    apply φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact Real.mul_self_sqrt hnn
  set ω : QuadraticAlgebra w.Completion dw 0 := ⟨0, 1⟩
  set c := algebraMap w.Completion (QuadraticAlgebra w.Completion dw 0) r
  have hprod : (ω - c) * (ω + c) = 0 := by
    ext
    · simp [ω, c, QuadraticAlgebra.algebraMap_eq, hr]
    · simp [ω, c, QuadraticAlgebra.algebraMap_eq]
  have hne : ω - c ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.im h
    simp [ω, c, QuadraticAlgebra.algebraMap_eq] at this
  have hne' : ω + c ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.im h
    simp [ω, c, QuadraticAlgebra.algebraMap_eq] at this
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
  apply hne'
  calc ω + c = (y * (ω - c)) * (ω + c) := by rw [mul_comm y, hy, one_mul]
    _ = 0 := by rw [mul_assoc, hprod, mul_zero]

omit [Algebra.IsQuadraticExtension K E] in

theorem isNonsplitAt_of_algEquiv {d : K} (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0)
    (hd : ringEquivRealOfIsReal hw (algebraMap K w.Completion d) < 0) : IsNonsplitAt E w :=
  MulEquiv.isField (MulEquiv.isField (Field.toIsField ℂ) (quadComplexEquiv _ hd).toMulEquiv)
    (tensorQuadEquiv ψ w.Completion).toMulEquiv

theorem isNonsplitAt_iff : IsNonsplitAt E w ↔ realPlaceD (E := E) hw < 0 :=
  ⟨realPlaceD_neg hw, isNonsplitAt_of_algEquiv hw (quadPsi K E w)⟩

end Place

section Phi

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {w : InfinitePlace K} (hw : w.IsReal) (hE : IsNonsplitAt E w)

noncomputable def realPlaceEquiv : w.Completion ⊗[K] E ≃+* ℂ :=
  (realPlaceTensorEquiv (E := E) (w := w)).toRingEquiv.trans
    (quadComplexEquiv (ringEquivRealOfIsReal hw) (realPlaceD_neg hw hE))

theorem realPlaceEquiv_conjBase (z : w.Completion ⊗[K] E) :
    realPlaceEquiv hw hE (conjBase K E w.Completion z) = starRingEnd ℂ (realPlaceEquiv hw hE z) := by
  simp only [realPlaceEquiv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
  rw [realPlaceTensorEquiv, tensorQuadEquiv_conjBase (R := w.Completion) (quadPsi_conj w)]
  exact quadComplexEquiv_star _ _ _

theorem realPlaceEquiv_algebraMap (t : w.Completion) :
    realPlaceEquiv hw hE (algebraMap w.Completion (w.Completion ⊗[K] E) t) =
      (ringEquivRealOfIsReal hw t : ℂ) := by
  simp only [realPlaceEquiv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact quadComplexEquiv_algebraMap _ _ t

theorem realPlaceEquiv_smul (t : w.Completion) (z : w.Completion ⊗[K] E) :
    realPlaceEquiv hw hE (t • z) = (ringEquivRealOfIsReal hw t : ℂ) * realPlaceEquiv hw hE z := by
  rw [Algebra.smul_def, map_mul, realPlaceEquiv_algebraMap]

theorem realPlaceEquiv_symm_ofReal (r : ℝ) :
    (realPlaceEquiv hw hE).symm (r : ℂ) =
      algebraMap w.Completion (w.Completion ⊗[K] E) ((ringEquivRealOfIsReal hw).symm r) := by
  apply (realPlaceEquiv hw hE).injective
  rw [RingEquiv.apply_symm_apply, realPlaceEquiv_algebraMap, RingEquiv.apply_symm_apply]

theorem continuous_ringEquivRealOfIsReal_symm :
    Continuous (ringEquivRealOfIsReal hw).symm :=
  (isometryEquivRealOfIsReal hw).symm.continuous

attribute [local instance] tensorTopology isModuleTopology_tensor isTopologicalRing_tensor

theorem continuous_realPlaceEquiv : Continuous (realPlaceEquiv hw hE) := by
  let φ := ringEquivRealOfIsReal hw
  let : Module w.Completion ℂ := Module.compHom ℂ (φ : w.Completion →+* ℝ)
  have hsmul : ∀ (t : w.Completion) (c : ℂ), t • c = (φ t : ℂ) * c := fun t c => by
    change (φ t : ℝ) • c = _
    rw [Complex.real_smul]
  have : ContinuousSMul w.Completion ℂ := ⟨by
    have : (fun p : w.Completion × ℂ => p.1 • p.2) = fun p => (φ p.1 : ℂ) * p.2 :=
      funext fun p => hsmul p.1 p.2
    rw [this]
    exact (Complex.continuous_ofReal.comp
      ((continuous_ringEquivRealOfIsReal hw).comp continuous_fst)).mul continuous_snd⟩
  let L : (w.Completion ⊗[K] E) →ₗ[w.Completion] ℂ :=
    { toFun := realPlaceEquiv hw hE
      map_add' := map_add _
      map_smul' := fun t z => by
        rw [RingHom.id_apply, hsmul, realPlaceEquiv_smul] }
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_realPlaceEquiv_symm : Continuous (realPlaceEquiv hw hE).symm := by
  let φ := ringEquivRealOfIsReal hw
  let : Module ℝ (w.Completion ⊗[K] E) :=
    Module.compHom _ (φ.symm : ℝ →+* w.Completion)
  have hsmul : ∀ (r : ℝ) (z : w.Completion ⊗[K] E), r • z = φ.symm r • z := fun _ _ => rfl
  have : ContinuousSMul ℝ (w.Completion ⊗[K] E) := ⟨by
    have : (fun p : ℝ × (w.Completion ⊗[K] E) => p.1 • p.2) = fun p => φ.symm p.1 • p.2 :=
      funext fun p => hsmul p.1 p.2
    rw [this]
    exact ((continuous_ringEquivRealOfIsReal_symm hw).comp continuous_fst).smul continuous_snd⟩
  have : T2Space (w.Completion ⊗[K] E) := t2Space_tensor w.Completion
  let L : ℂ →ₗ[ℝ] (w.Completion ⊗[K] E) :=
    { toFun := (realPlaceEquiv hw hE).symm
      map_add' := map_add _
      map_smul' := fun r c => by
        rw [RingHom.id_apply, hsmul, Complex.real_smul, map_mul, realPlaceEquiv_symm_ofReal,
          Algebra.smul_def] }
  exact LinearMap.continuous_of_finiteDimensional L

end Phi

section Unitary

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {w : InfinitePlace K} (hw : w.IsReal) (hE : IsNonsplitAt E w)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

noncomputable def realPlaceMatrix : Matrix ι ι ℂ :=
  (H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] w.Completion ⊗[K] E)).map
    (realPlaceEquiv hw hE)

attribute [local instance] tensorTopology isModuleTopology_tensor isTopologicalRing_tensor

noncomputable def unitaryPointsRealEquiv :
    unitaryPoints K E H w.Completion ≃ₜ*
      unitaryGroupMatrix (starRingEnd ℂ) (realPlaceMatrix hw hE H) where
  toMulEquiv := unitaryGroupMatrixCongr (realPlaceEquiv hw hE) (realPlaceEquiv_conjBase hw hE) rfl
  continuous_toFun := by
    have hv : Continuous fun g : unitaryPoints K E H w.Completion =>
        ((g : GL ι (w.Completion ⊗[K] E)) : Matrix ι ι (w.Completion ⊗[K] E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun g : unitaryPoints K E H w.Completion =>
        ((g : GL ι (w.Completion ⊗[K] E)) : Matrix ι ι (w.Completion ⊗[K] E)).map
          (realPlaceEquiv hw hE) :=
      hv.matrix_map (continuous_realPlaceEquiv hw hE)
    have h2 : Continuous fun g : unitaryPoints K E H w.Completion =>
        ((((g : GL ι (w.Completion ⊗[K] E))⁻¹ : GL ι (w.Completion ⊗[K] E))) :
          Matrix ι ι (w.Completion ⊗[K] E)).map (realPlaceEquiv hw hE) :=
      ((Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_map
        (continuous_realPlaceEquiv hw hE)
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _
  continuous_invFun := by
    have h1 : Continuous fun g : unitaryGroupMatrix (starRingEnd ℂ) (realPlaceMatrix hw hE H) =>
        ((g : GL ι ℂ) : Matrix ι ι ℂ).map (realPlaceEquiv hw hE).symm :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_map
        (continuous_realPlaceEquiv_symm hw hE)
    have h2 : Continuous fun g : unitaryGroupMatrix (starRingEnd ℂ) (realPlaceMatrix hw hE H) =>
        ((((g : GL ι ℂ))⁻¹ : GL ι ℂ) : Matrix ι ι ℂ).map (realPlaceEquiv hw hE).symm :=
      (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map
        (continuous_realPlaceEquiv_symm hw hE)
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _

variable {H}

end Unitary

section Example

instance fact_sq_ne_neg_one : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

end Example

end GroundTheory.Heights₂.Theta
