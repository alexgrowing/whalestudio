import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  exact (IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem stdH_adj (D : D7) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) (x : Fin N → D.host.E)
    (y : Fin N' → D.host.E) :
    stdH D.host.E N x ((A.map D.host.conj)ᵀ *ᵥ y) = stdH D.host.E N' (A *ᵥ x) y := by
  unfold stdH
  simp only [star_eq_hostConj, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem stdH_natsmul_left (D : D7) {N : ℕ} (s : ℕ) (x y : Fin N → D.host.E) :
    stdH D.host.E N ((s : D.host.E) • x) y = (s : D.host.E) * stdH D.host.E N x y := by
  unfold stdH
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem stdH_natsmul_right (D : D7) {N : ℕ} (s : ℕ) (x y : Fin N → D.host.E) :
    stdH D.host.E N x ((s : D.host.E) • y) = (s : D.host.E) * stdH D.host.E N x y := by
  unfold stdH
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem adj_maps_sd : ∀ (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) (s : ℕ), IsSDLat D.host.E N L → IsSDLat D.host.E N' L' → (∀ x ∈ L, (s : D.host.E) • (A *ᵥ x) ∈ L') → ∀ y ∈ L', (s : D.host.E) • ((A.map D.host.conj)ᵀ *ᵥ y) ∈ L := by
  intro D N N' L L' A s hL hL' hA y hy
  refine (hL.2.2 _).2 fun x hx => ?_
  rw [stdH_natsmul_right, stdH_adj, ← stdH_natsmul_left]
  exact (hL'.2.2 y).1 hy _ (hA x hx)

end GlobalTheory.TwV

end
