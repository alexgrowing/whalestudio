import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actOn_tmul_tmul' {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r a : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (a ⊗ₜ v) = (r * a) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.coe_comp, Function.comp_apply,
    Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  change r • (rep c).baseChange R (a ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem adj_actOn_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  intro p _ D G L x v w
  induction x using TensorProduct.induction_on generalizing v w with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, MulOpposite.unop_add, hx, hy]
  | tmul r c =>
    rw [starT_tmul]
    induction v using TensorProduct.induction_on generalizing w with
    | zero => simp
    | add v v' hv hv' => simp only [map_add, LinearMap.add_apply, hv, hv']
    | tmul a v₀ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [map_add, hw, hw']
      | tmul a' w₀ =>
        rw [actOn_tmul_tmul', actOn_tmul_tmul', LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, L.adj c v₀ w₀, mul_left_comm, _root_.mul_assoc]
        rfl

end GlobalTheory.LKGeo
