import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnectingSumMultDiag

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem cobOne_diagSum_eq (p : ℕ) (R : Type) [CommRing R] (G : PDivGroup p R) (n m : ℕ) (hm : (m : R) = 0) :
    ∀ c ∈ symCocycles R (G.A n), cobOne R (G.A n) (diagSum R (G.A n) m c) = pullbackTwo (mulBy R (G.A n) m) c -
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
        (fun _ _ ↦ Commute.all _ _) c) • (1 : G.A n ⊗[R] G.A n) := by
  intro c hc
  have hd : diagSum R (G.A n) m c = ∑ i ∈ Finset.range m, multDiag R (G.A n) i c := by
    simp [diagSum, LinearMap.sum_apply]
  have hz : m • c = 0 := by rw [← Nat.cast_smul_eq_nsmul R, hm, zero_smul]
  rw [pullTwo_mulBy_eq c hc m, hz, add_zero, hd, Algebra.algebraMap_eq_smul_one]
  abel

end GlobalTheory.PtExt
