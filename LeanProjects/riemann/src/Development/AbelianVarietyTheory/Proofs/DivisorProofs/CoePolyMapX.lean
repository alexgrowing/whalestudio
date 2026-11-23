import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def rightInc (A : Subalgebra ℂ K) : κ' →+* tens (κ' := κ') A :=
  (Algebra.TensorProduct.includeRight : κ' →ₐ[ℂ] K ⊗[ℂ] κ').toRingHom.codRestrict
    (tens (κ' := κ') A).toSubring fun b => tmul_mem (one_mem A) b

def polyMap (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) :
    MvPolynomial (Fin m) κ' →+* tens (κ' := κ') A :=
  MvPolynomial.eval₂Hom (rightInc A) fun i => ⟨(v i : K) ⊗ₜ 1, tmul_mem (v i).2 1⟩

@[simp] theorem coe_rightInc (A : Subalgebra ℂ K) (b : κ') :
    (rightInc A b : K ⊗[ℂ] κ') = 1 ⊗ₜ b := rfl

@[simp] theorem coe_polyMap_X (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (i : Fin m) :
    (polyMap (κ' := κ') A v (MvPolynomial.X i) : K ⊗[ℂ] κ') = (v i : K) ⊗ₜ 1 := by
  simp [polyMap]

@[simp] theorem coe_polyMap_C (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (b : κ') :
    (polyMap (κ' := κ') A v (MvPolynomial.C b) : K ⊗[ℂ] κ') = 1 ⊗ₜ b := by
  simp [polyMap]

end GlobalTheory.GraphLocal
