import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverPStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIndependentBasisLatticeFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalWeilPairingTorsionConstHolomorphicFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionCubicalWeilOneComplexPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det) (hhol : IsHolTo Set.univ (fun z => (e z).left))
    (he : IsExpAt t y e) : IsExpAt t y (fun w => e (M *ᵥ w)) := by
  have hchain : ∀ w v, IsDerivAt0 (fun u => (e (M *ᵥ u)).left) w v ↔
      IsDerivAt0 (fun u => (e u).left) (M *ᵥ w) v := by
    intro w v
    rw [GlobalTheory.HolHom.isDerivAt0_iff, GlobalTheory.HolHom.isDerivAt0_iff]
    exact GlobalTheory.ShFam.BdArc.LatSec.isDerivAt_comp_iff (GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ 0))
      (Matrix.mulVecLin M).toContinuousLinearMap w v
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨fun v w => ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [Matrix.mulVec_add]
    exact he.1 _ _
  · simp_rw [hchain]
    exact he.2.1 (M *ᵥ w)
  · obtain ⟨w', hw', huniq⟩ := he.2.2 v hv
    refine ⟨M⁻¹ *ᵥ w', ?_, fun w₂ hw₂ => ?_⟩
    · show IsDerivAt0 (fun u => (e (M *ᵥ u)).left) (M⁻¹ *ᵥ w') v
      rw [hchain, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
      exact hw'
    · have h2 : M *ᵥ w₂ = w' := huniq _ ((hchain w₂ v).1 hw₂)
      rw [← h2, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]

end GlobalTheory.ShFam.Hor.LogCh
