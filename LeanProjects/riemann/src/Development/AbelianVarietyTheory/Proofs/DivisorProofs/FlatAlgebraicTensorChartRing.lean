import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem PreChart.tensor_flat_isAlgebraic (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) :
    Module.Flat R (c.C ⊗[R] c.C) ∧ Algebra.IsAlgebraic R (c.C ⊗[R] c.C) := by
  have hM : Submonoid.powers c.r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors c.r_ne_zero
  haveI : IsDomain (Localization.Away c.r) := IsLocalization.isDomain_localization hM
  haveI : Module.Flat R (Localization.Away c.r) := IsLocalization.flat _ (Submonoid.powers c.r)
  haveI : Module.Flat R c.C := Module.Flat.trans R (Localization.Away c.r) c.C
  haveI : Algebra.IsAlgebraic R (Localization.Away c.r) := IsLocalization.isAlgebraic _ (Submonoid.powers c.r)
  haveI : Algebra.IsAlgebraic (Localization.Away c.r) c.C :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := Localization.Away c.r) x).isAlgebraic⟩
  haveI : Algebra.IsAlgebraic R c.C := Algebra.IsAlgebraic.trans R (Localization.Away c.r) c.C
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isAlgebraic_zero
  | add x y hx hy => exact hx.add hy
  | tmul x y =>
    have hx := (Algebra.IsAlgebraic.isAlgebraic (R := R) x).algHom
      (Algebra.TensorProduct.includeLeft : c.C →ₐ[R] c.C ⊗[R] c.C)
    have hy := (Algebra.IsAlgebraic.isAlgebraic (R := R) y).algHom
      (Algebra.TensorProduct.includeRight : c.C →ₐ[R] c.C ⊗[R] c.C)
    simpa using hx.mul hy

end GlobalTheory.GroupBplus.Aff
