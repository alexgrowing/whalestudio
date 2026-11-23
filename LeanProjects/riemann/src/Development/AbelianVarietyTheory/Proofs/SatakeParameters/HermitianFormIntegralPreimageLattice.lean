import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint

open Matrix

namespace GlobalTheory.Hk3.HoweG.GramA

variable {L : Type} [Field L]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (a b : Fin n → L) :
    Formalism.UG.hform σ J a b = (fun i => σ (a i)) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem map_mulVec_eq (σ : L →+* L) {n m : ℕ} (A : Matrix (Fin n) (Fin m) L) (w : Fin m → L) :
    (fun i => σ ((A *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT σ A := by
  ext i
  simp [Formalism.UG.cT, dotProduct, Matrix.mulVec, Matrix.vecMul, map_sum, mul_comm]

theorem dot_mem (O : Subring L) {n : ℕ} {a b : Fin n → L} (ha : ∀ i, a i ∈ O) (hb : ∀ i, b i ∈ O) : a ⬝ᵥ b ∈ O :=
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha k) (hb k)

theorem mulVec_mem (O : Subring L) {n m : ℕ} {A : Matrix (Fin n) (Fin m) L} {b : Fin m → L}
    (hA : ∀ i j, A i j ∈ O) (hb : ∀ i, b i ∈ O) : ∀ i, (A *ᵥ b) i ∈ O :=
  fun i => dot_mem O (hA i) hb

theorem hform_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  have hS' := HoweSwap.cT_herm hS
  have hT' := HoweSwap.cT_herm hT
  have hSi := HoweSwap.cT_inv_herm JS hS'
  have iS : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJS).1
  have iT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJT).1
  have hσO : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rw [hv]; exact hz
  have e1 : (JS : Matrix (Fin n) (Fin n) L) * adj σ JS JT x = Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj
    rw [Matrix.mul_assoc, HoweSwap.mul_inv_cl]
  have e2 : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    unfold adj
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hT', hSi, HoweSwap.cT_cT hσ, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  have e3 : x * adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
      (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj Formalism.UG.cT
    simp only [Matrix.mul_assoc]
  have h1 : ∀ b : Fin n → L, Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + adj σ JS JT x *ᵥ w) b =
      (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ b) +
        (fun i => σ (w i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ (x *ᵥ b)) := by
    intro b
    have : (fun i => σ ((u + adj σ JS JT x *ᵥ w) i)) = (fun i => σ (u i)) + fun i => σ ((adj σ JS JT x *ᵥ w) i) := by
      ext i; simp
    rw [hform_eq_dot, this, add_dotProduct, map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2,
      Matrix.mulVec_mulVec]
  have h2 : (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ (adj σ JS JT x *ᵥ w')) =
      (fun i => σ ((x *ᵥ u) i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]
  have h3 : x *ᵥ (adj σ JS JT x *ᵥ w') =
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *ᵥ
        ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e3]
  rw [h1, Matrix.mulVec_add, dotProduct_add, h2, Matrix.mulVec_add, h3]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact dot_mem _ (fun i => hσO _ (hu i)) (mulVec_mem _ iS hu')
  · exact dot_mem _ (fun i => hσO _ (hxu i)) (mulVec_mem _ iT hw')
  · refine dot_mem _ (fun i => hσO _ (hw i)) (mulVec_mem _ iT fun i => ?_)
    exact add_mem (hxu' i) (mulVec_mem _ hx (mulVec_mem _ iT hw') i)

end GlobalTheory.Hk3.HoweG.GramA
