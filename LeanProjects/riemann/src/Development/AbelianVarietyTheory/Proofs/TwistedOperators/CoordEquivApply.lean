import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

def powB : Module.Basis (Fin r) E (Fld P) :=
  (AdjoinRoot.powerBasis P.2.2.1.ne_zero).basis.reindex
    (finCongr ((AdjoinRoot.powerBasis_dim P.2.2.1.ne_zero).trans P.2.2.2.1))

def gramOne : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i j => Algebra.trace E (Fld P) (powB P j * star' P (powB P i))

variable (k : Type) [CommRing k] [Algebra F k]

def coordF (i : Fin r) : k ⊗[F] Fld P →ₗ[F] k ⊗[F] E :=
  LinearMap.lTensor k (((powB P).coord i).restrictScalars F)

theorem coordF_tmul (i : Fin r) (a : k) (z : Fld P) : coordF P k i (a ⊗ₜ[F] z) = a ⊗ₜ[F] (powB P).repr z i := rfl

theorem smul_eq_map_mul (c : k ⊗[F] E) (y : k ⊗[F] Fld P) :
    c • y = Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P)) c * y :=
  Algebra.smul_def c y

theorem coordF_smul (i : Fin r) (c : k ⊗[F] E) (y : k ⊗[F] Fld P) : coordF P k i (c • y) = c * coordF P k i y := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' h h' => rw [add_smul, map_add, h, h', add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' h h' => rw [smul_add, map_add, h, h', map_add, mul_add]
    | tmul a' z =>
      rw [smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, coordF_tmul,
        coordF_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      change (powB P).repr (algebraMap E (Fld P) e * z) i = e * _
      rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

def coordInv (w : Fin r → k ⊗[F] E) : k ⊗[F] Fld P := ∑ i, w i • ((1 : k) ⊗ₜ[F] powB P i)

theorem coordF_coordInv (w : Fin r → k ⊗[F] E) (j : Fin r) : coordF P k j (coordInv P k w) = w j := by
  simp only [coordInv, map_sum, coordF_smul, coordF_tmul, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j (fun i _ h => by rw [Finsupp.single_apply, if_neg h, TensorProduct.tmul_zero, mul_zero])
    (by simp), Finsupp.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]

theorem coordInv_coordF (y : k ⊗[F] Fld P) : coordInv P k (fun i => coordF P k i y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add y y' h h' =>
    conv_rhs => rw [← h, ← h']
    simp only [coordInv, map_add, add_smul, Finset.sum_add_distrib]
  | tmul a z =>
    simp only [coordInv, coordF_tmul, smul_eq_map_mul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
    rw [← TensorProduct.tmul_sum]
    congr 1
    conv_rhs => rw [← (powB P).sum_repr z]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

def coordEquiv : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E) where
  toFun y i := coordF P k i y
  map_add' y y' := funext fun i => map_add _ _ _
  map_smul' c y := funext fun i => coordF_smul P k i c y
  invFun := coordInv P k
  left_inv y := coordInv_coordF P k y
  right_inv w := funext fun j => coordF_coordInv P k w j

theorem coordEquiv_apply (y : k ⊗[F] Fld P) (i : Fin r) : coordEquiv P k y i = coordF P k i y := rfl

end GlobalTheory.TrUnitLat
