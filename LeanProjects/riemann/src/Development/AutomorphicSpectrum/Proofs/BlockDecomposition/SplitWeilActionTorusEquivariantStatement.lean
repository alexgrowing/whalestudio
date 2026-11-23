import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariant
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_action_torus_equivariant : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) (Φ : F × F → ℂ) (τ : Fˣ) (x : F × F),
  GL2LocalData.piS χ c₁ g (fun y => Φ (y * ((τ : F), ((τ⁻¹ : Fˣ) : F)))) x = GL2LocalData.piS χ c₁ g Φ (x * ((τ : F), ((τ⁻¹ : Fˣ) : F))) := by
  first | exact @GlobalTheory.CompanionTheory.SplitTorus.piS_torus | exact GlobalTheory.CompanionTheory.SplitTorus.piS_torus | (intros; apply GlobalTheory.CompanionTheory.SplitTorus.piS_torus <;> assumption)
