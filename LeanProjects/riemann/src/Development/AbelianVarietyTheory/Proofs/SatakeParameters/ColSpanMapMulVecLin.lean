import Mathlib
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

namespace GlobalTheory.TwV

theorem colSpan_map_mulVecLin {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A g : Matrix (Fin k) (Fin k) K) :
    (Formalism.MainNotions.G.colSpan R g).map (A.mulVecLin.restrictScalars R) = Formalism.MainNotions.G.colSpan R (A * g) := by
  unfold Formalism.MainNotions.G.colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem locSp_reindex : ∀ {E : Type} [Field E] [NumberField E] (σ : E →+* E) (W K : Type) [CommRing W] [Field K] [Algebra W K] (ρ : E →+* K) {n N : ℕ} (h : n = N) (J : Matrix (Fin N) (Fin N) E) (B : GL (Fin N) E) (g : GL (Fin n) K) (Λ : Submodule (𝓞 E) (Fin N → E)) (Λ' : Submodule (𝓞 E) (Fin n → E)), HEq Λ' Λ → locSp W ρ Λ = colSpan W ((LinearMap.toMatrix' (stdCo σ J).toLinearMap * B.1).map ρ * (castGL h K g : Matrix (Fin N) (Fin N) K)) → locSp W ρ Λ' = (colSpan W (g : Matrix (Fin n) (Fin n) K)).map (((((LinearMap.toMatrix' (stdCo σ (J.reindex (finCongr h.symm) (finCongr h.symm))).toLinearMap * (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) B).1).map ρ).submatrix (finCongr (rfl : n = n)) (finCongr (rfl : n = n))).mulVecLin).restrictScalars W) := by
  intro E _ _ σ W K _ _ _ ρ n N h J B g Λ Λ' hΛ hs
  subst h
  obtain rfl := eq_of_heq hΛ
  rw [colSpan_map_mulVecLin, hs]
  rfl

end GlobalTheory.TwV
