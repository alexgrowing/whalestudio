import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RootUnip

open GlobalTheory.BesselCompare (hA_add hA_smul hA_smul_right)

variable {D : D7} {B : HSp D}

def kMat (B : HSp D) (v y : Fin B.rank → AE D) : Matrix (Fin B.rank) (Fin B.rank) (AE D) :=
  1 + vecMulVec v ((fun i => cA D (y i)) ᵥ* B.gram.map (incA D)) -
    vecMulVec y ((fun i => cA D (v i)) ᵥ* B.gram.map (incA D))

theorem kMat_mulVec (v y x : Fin B.rank → AE D) :
    (kMat B v y).mulVec x = x + hA B x y • v - hA B x v • y := by
  rw [kMat, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec, hA_eq, hA_eq, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  simp only [op_smul_eq_smul]

theorem continuous_rankTwo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    {c : R → R} (hc : Continuous c) (J : Matrix (Fin n) (Fin n) R) (v w : Fin n → R) :
    Continuous fun y : Fin n → R => 1 + vecMulVec v ((fun i => c (y i)) ᵥ* J) - vecMulVec y w := by
  have hc' : Continuous fun y : Fin n → R => fun i => c (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  have h1 := continuous_const (y := v).matrix_vecMulVec (hc'.matrix_vecMul (continuous_const (y := J)))
  have h2 := (continuous_id (X := Fin n → R)).matrix_vecMulVec (continuous_const (y := w))
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.sub_apply, Matrix.add_apply]
  exact (continuous_const.add (h1.matrix_elem i j)).sub (h2.matrix_elem i j)

theorem continuous_kMat (v : Fin B.rank → AE D) : Continuous (kMat B v) :=
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  continuous_rankTwo GlobalTheory.FockCompare.ThetaCont.continuous_conj _ _ _

section

variable {η : AE D} (hη : η * cA D η = 0) {v y : Fin B.rank → AE D} (hy : η • y = y) (hv : hA B v y = 0)

include hη hy in
theorem hA_smul_self (x : Fin B.rank → AE D) : hA B x y • y = 0 := by
  have e : hA B x y = cA D η * hA B x y := by rw [← hA_smul_right, hy]
  rw [e, ← hy, smul_smul, hy, mul_assoc, mul_comm (hA B x y), ← mul_assoc, mul_comm (cA D η), hη, zero_mul,
    zero_smul]

include hη hy in
theorem hA_mul_hA (x x' : Fin B.rank → AE D) : hA B x y * hA B y x' = 0 := by
  rw [← hA_smul, hA_smul_self hη hy, hA_zero]

include hη hy in
theorem hA_self : hA B y y = 0 := by
  have e : hA B y y = η * (cA D η * hA B y y) := by rw [← hA_smul_right, ← hA_smul, hy]
  rw [e, ← mul_assoc, hη, zero_mul]

include hv in
theorem hA_yv : hA B y v = 0 := by rw [← hA_herm, hv, map_zero]

include hη hy hv in
theorem kMat_neg_mul : kMat B v (-y) * kMat B v y = 1 := by
  refine Matrix.mulVec_injective (funext fun x => ?_)
  show (kMat B v (-y) * kMat B v y).mulVec x = (1 : Matrix _ _ _).mulVec x
  rw [← Matrix.mulVec_mulVec, kMat_mulVec, kMat_mulVec, Matrix.one_mulVec, hA_neg_right]
  simp only [hA_sub, hA_add, hA_smul, hv, hA_yv hv, hA_self hη hy, mul_zero, add_zero, sub_zero]
  have h0 : (hA B x y * hA B v v) • y = 0 := by
    rw [mul_comm, mul_smul, hA_smul_self hη hy, smul_zero]
  rw [smul_neg, add_smul, h0, neg_smul]
  abel

include hη hy hv in
theorem kMat_mul_neg : kMat B v y * kMat B v (-y) = 1 := by
  have := kMat_neg_mul (y := -y) (v := v) hη (by rw [smul_neg, hy]) (by rw [hA_neg_right, hv, neg_zero])
  rwa [neg_neg] at this

include hη hy hv in
theorem hA_kMat (x x' : Fin B.rank → AE D) :
    hA B ((kMat B v y).mulVec x) ((kMat B v y).mulVec x') = hA B x x' := by
  rw [kMat_mulVec, kMat_mulVec]
  simp only [hA_sub, hA_add, hA_smul, hA_sub_right, hA_add_right, hA_smul_right, hA_herm, hv, hA_yv hv,
    hA_self hη hy]
  linear_combination hA B v v * hA_mul_hA hη hy x x'

end

theorem unitary_of_hA {M : Matrix (Fin B.rank) (Fin B.rank) (AE D)}
    (h : ∀ x y, hA B (M.mulVec x) (M.mulVec y) = hA B x y) :
    (M.map (cA D))ᵀ * B.gram.map (incA D) * M = B.gram.map (incA D) := by
  have key : ∀ x y : Fin B.rank → AE D,
      (fun i => cA D (y i)) ⬝ᵥ ((M.map (cA D))ᵀ * B.gram.map (incA D) * M).mulVec x =
        (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := fun x y => by
    have e : (fun i => cA D (M.mulVec y i)) = (M.map (cA D)).mulVec fun i => cA D (y i) :=
      funext fun i => RingHom.map_mulVec (cA D) _ y i
    have := h x y
    rwa [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at this
  refine Matrix.mulVec_injective (funext fun x => funext fun i => ?_)
  have := key x (Pi.single i 1)
  rwa [show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct, single_one_dotProduct] at this

theorem exists_continuous_isK (D : D7) (B : HSp D) (η : AE D) (hη : η * cA D η = 0) (v : Fin B.rank → AE D) :
    ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B,
      Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  refine ⟨fun y => ⟨⟨kMat B v y.1, kMat B v (-y.1), kMat_mul_neg hη y.2.1 y.2.2, kMat_neg_mul hη y.2.1 y.2.2⟩,
    unitary_of_hA (hA_kMat hη y.2.1 y.2.2)⟩, ?_, fun y x => kMat_mulVec v y.1 x⟩
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_kMat v).comp continuous_subtype_val
  · exact (continuous_kMat v).comp continuous_subtype_val.neg

end GlobalTheory.RootUnip

end
