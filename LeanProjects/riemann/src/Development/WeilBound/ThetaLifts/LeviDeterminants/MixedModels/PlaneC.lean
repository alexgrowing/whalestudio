import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace PositivityTheory.Mix.Adapt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n n₁ d : ℕ} {H : Plane E n n₁}

theorem extend_eq {κ κ₀ κ₁ R : Type} [Zero R] (ε : κ ≃ κ₀ ⊕ κ₁) (a : κ₁ → R) :
    Function.extend (fun k => ε.symm (.inr k)) a 0 = glue ε 0 a := by
  funext k
  obtain ⟨k, rfl⟩ := ε.symm.surjective k
  rcases k with k | k
  · rw [glue_inl, Function.extend_apply' _ _ _ (by rintro ⟨x, hx⟩; simpa using hx)]; rfl
  · rw [glue_inr]
    exact (ε.symm.injective.comp Sum.inr_injective).extend_apply a 0 k

omit [NumberField E] in
theorem incM_one {α : Type} [DecidableEq α] : incM F (1 : Matrix α α E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

omit [NumberField E] in
theorem dec (w : Matrix (Fin n₁ ⊕ Fin 2) (Fin d) (AE F E)) : incM F (frame H) * w =
    Matrix.vecMulVec (incV F H.x) (w (.inr 0)) + incM F H.ι * w.submatrix .inl id + Matrix.vecMulVec (incV F H.y) (w (.inr 1)) := by
  ext i l
  simp [frame, incM, incV, Matrix.mul_apply, Matrix.vecMulVec_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

def what₂ {R : Type} (z : Matrix (Fin n₁) (Fin d) R) (a b : Fin d → R) : Matrix (Fin n₁ ⊕ Fin 2) (Fin d) R :=
  Matrix.of fun i => Sum.elim z ![a, b] i

@[simp] theorem rows_inl {R : Type} (z : Matrix (Fin n₁) (Fin d) R) (a b : Fin d → R) (i : Fin n₁) : what₂ z a b (.inl i) = z i := rfl

@[simp] theorem rows_zero {R : Type} (z : Matrix (Fin n₁) (Fin d) R) (a b : Fin d → R) : what₂ z a b (.inr 0) = a := rfl

@[simp] theorem rows_one {R : Type} (z : Matrix (Fin n₁) (Fin d) R) (a b : Fin d → R) : what₂ z a b (.inr 1) = b := rfl

@[simp] theorem rows_sub {R : Type} (z : Matrix (Fin n₁) (Fin d) R) (a b : Fin d → R) : (what₂ z a b).submatrix .inl id = z := rfl

omit [NumberField E] in
theorem frame_alt (z : Fin d → AE F E) : incM F (frame H) * what₂ (0 : Matrix (Fin n₁) (Fin d) (AE F E)) z 0 = Matrix.vecMulVec (incV F H.x) z := by
  rw [dec]; ext i l; simp [Matrix.vecMulVec_apply]

omit [NumberField E] in
theorem frame_y (z : Fin d → AE F E) : incM F (frame H) * what₂ (0 : Matrix (Fin n₁) (Fin d) (AE F E)) 0 z = Matrix.vecMulVec (incV F H.y) z := by
  rw [dec]; ext i l; simp [Matrix.vecMulVec_apply]

omit [NumberField E] in
theorem frame_iota (z : Matrix (Fin n₁) (Fin d) (AE F E)) : incM F (frame H) * what₂ z 0 0 = incM F H.ι * z := by
  rw [dec]; ext i l; simp [Matrix.vecMulVec_apply]

variable {A : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) (AE F E)}

omit [NumberField E] in
theorem adapted_frame_mul_vecMulVec (hA : A * incM F (frame H) = 1) (z : Fin d → AE F E) : A * Matrix.vecMulVec (incV F H.x) z = what₂ (0 : Matrix (Fin n₁) (Fin d) (AE F E)) z 0 := by
  rw [← frame_alt, ← Matrix.mul_assoc, hA, Matrix.one_mul]

omit [NumberField E] in
theorem mul_y (hA : A * incM F (frame H) = 1) (z : Fin d → AE F E) : A * Matrix.vecMulVec (incV F H.y) z = what₂ (0 : Matrix (Fin n₁) (Fin d) (AE F E)) 0 z := by
  rw [← frame_y, ← Matrix.mul_assoc, hA, Matrix.one_mul]

omit [NumberField E] in
theorem mul_iota (hA : A * incM F (frame H) = 1) (z : Matrix (Fin n₁) (Fin d) (AE F E)) : A * (incM F H.ι * z) = what₂ z 0 0 := by
  rw [← frame_iota, ← Matrix.mul_assoc, hA, Matrix.one_mul]

end PositivityTheory.Mix.Adapt
