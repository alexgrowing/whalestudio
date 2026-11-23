import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonalStatement

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar

section Equiv

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def mulVecEquiv (A : Matrix ι ι R) (h : IsUnit A.det) : (ι → R) ≃ₜ+ (ι → R) where
  toFun x := A *ᵥ x
  invFun x := A⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A h]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A h]
  map_add' x y := Matrix.mulVec_add A x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem transvection_mulVec_apply (i j : ι) (c : R) (f : ι → R) (k : ι) :
    (Matrix.transvection i j c *ᵥ f) k = f k + if k = i then c * f j else 0 := by
  by_cases hk : k = i
  · subst hk
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hk]

end Equiv

section Measure

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurePreserving_transvection (ν : Measure R) [ν.IsAddHaarMeasure] {i j : ι}
    (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => Matrix.transvection i j c *ᵥ x)
      (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) := by
  let p : ι → Prop := fun k => k ≠ i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → R) → (β → R) → β → R := fun a b => (fun _ => c * a ⟨j, hij.symm⟩) + b
  let F : (α → R) × (β → R) → (α → R) × (β → R) := fun q => (id q.1, g q.1 q.2)
  let e : (ι → R) ≃ᵐ (α → R) × (β → R) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => R) p
  have key : (fun x : ι → R => Matrix.transvection i j c *ᵥ x) = e.symm ∘ F ∘ e := by
    ext f k
    rw [transvection_mulVec_apply]
    by_cases hk : k = i
    · subst hk
      simp [e, F, g, p, α, β, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
    · simp [e, F, g, p, α, β, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hk]
  rw [key]
  have A : MeasurePreserving e (Measure.pi fun _ => ν) _ :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => ν) p
  have B : MeasurePreserving F
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have g_meas : Measurable (Function.uncurry g) := by
      have : Continuous (Function.uncurry g) := by
        unfold Function.uncurry
        simp only [g]
        fun_prop
      exact this.measurable
    exact (MeasurePreserving.id _).skew_product g_meas
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact (A.symm e).comp (B.comp A)

open Classical in

noncomputable def scale (A : Matrix ι ι R) : ℝ≥0 :=
  if h : IsUnit A.det then addEquivAddHaarChar (mulVecEquiv A h) else 1

theorem scale_of_isUnit {A : Matrix ι ι R} (h : IsUnit A.det) :
    scale A = addEquivAddHaarChar (mulVecEquiv A h) := dif_pos h

theorem scale_mul {A B : Matrix ι ι R} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    scale (A * B) = scale A * scale B := by
  have hAB : IsUnit (A * B).det := by
    rw [Matrix.det_mul]
    exact hA.mul hB
  have e : mulVecEquiv (A * B) hAB = (mulVecEquiv B hB).trans (mulVecEquiv A hA) :=
    ContinuousAddEquiv.ext fun x => (Matrix.mulVec_mulVec x A B).symm
  rw [scale_of_isUnit hAB, scale_of_isUnit hA, scale_of_isUnit hB, e, addEquivAddHaarChar_trans,
    mul_comm]

theorem scale_transvection {i j : ι} (hij : i ≠ j) (c : R) :
    scale (Matrix.transvection i j c) = 1 := by
  have h : IsUnit (Matrix.transvection i j c).det := by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact isUnit_one
  have hmp := measurePreserving_transvection (Measure.addHaar : Measure R) hij c
  have e : (Measure.pi fun _ : ι => (Measure.addHaar : Measure R)).map (mulVecEquiv _ h) =
      Measure.pi fun _ : ι => (Measure.addHaar : Measure R) := hmp.map_eq
  have one : ∀ (m : Measure (ι → R)) [m.IsAddHaarMeasure],
      m = Measure.pi (fun _ : ι => (Measure.addHaar : Measure R)) →
      Measure.addHaarScalarFactor (Measure.pi fun _ : ι => (Measure.addHaar : Measure R)) m = 1 := by
    rintro m _ rfl
    exact Measure.addHaarScalarFactor_self _
  rw [scale_of_isUnit h,
    addEquivAddHaarChar_eq (Measure.pi fun _ : ι => (Measure.addHaar : Measure R))]
  exact one _ e

theorem transpose_transvection (i j : ι) (c : R) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one]

theorem scale_transpose (hsr : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    (A : Matrix ι ι R) (hA : IsUnit A.det) : scale Aᵀ = scale A := by
  refine GlobalTheory.T.matrix_induction_transvection_diagonal R hsr ι (fun A => scale Aᵀ = scale A) ?_ ?_ ?_ A hA
  · intro i j c hij
    simp only [transpose_transvection]
    rw [scale_transvection hij, scale_transvection hij.symm]
  · intro D _
    simp only [Matrix.diagonal_transpose]
  · intro A B hA hB (eA : scale Aᵀ = scale A) (eB : scale Bᵀ = scale B)
    show scale (A * B)ᵀ = scale (A * B)
    rw [Matrix.transpose_mul, scale_mul (by rwa [Matrix.det_transpose])
      (by rwa [Matrix.det_transpose]), scale_mul hA hB, eA, eB, mul_comm]

end Measure

theorem map_mulVec_eq_of_transpose_mul_mul_eq :
    ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
      [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R],
      (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → R)) [μ.IsAddHaarMeasure]
        (B g : Matrix ι ι R), IsUnit B.det → gᵀ * B * g = B →
        μ.map (fun x => g *ᵥ x) = μ := by
  intro R _ _ _ _ _ _ _ _ hsr ι _ _ μ _ B g hB h
  have hg2 : g.det * g.det = 1 := by
    have e := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    have e2 : B.det * (g.det * g.det) = B.det * 1 := by linear_combination e
    exact hB.mul_left_cancel e2
  have hg : IsUnit g.det := isUnit_iff_exists_inv.mpr ⟨_, hg2⟩
  have hgt : IsUnit gᵀ.det := by rwa [Matrix.det_transpose]
  have hpos : 0 < scale B := by
    rw [scale_of_isUnit hB]
    exact addEquivAddHaarChar_pos _
  have hsq : scale g ^ 2 = 1 := by
    have e := congrArg scale h
    rw [scale_mul (by rw [Matrix.det_mul]; exact hgt.mul hB) hg, scale_mul hgt hB,
      scale_transpose hsr g hg] at e
    apply mul_left_cancel₀ hpos.ne'
    calc scale B * scale g ^ 2 = scale g * scale B * scale g := by ring
      _ = scale B := e
      _ = scale B * 1 := (mul_one _).symm
  have h1 : scale g = 1 := (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 hsq
  have hmap := addEquivAddHaarChar_smul_map μ (mulVecEquiv g hg)
  rw [← scale_of_isUnit hg, h1, one_smul] at hmap
  exact hmap

end GlobalTheory.CompanionTheory.Adelic.OrthHaar
