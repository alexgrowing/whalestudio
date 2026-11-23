import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta

theorem lc_pri (v : Pl) (α : ℚˣ) : ((Ad3.R.lc v (pri α) : (Qv v)ˣ) : Qv v) = (((α : ℚˣ) : ℚ) : Qv v) := by
  have h : ∀ f : ℚ →+* Qv v, f (α : ℚ) = (((α : ℚˣ) : ℚ) : Qv v) := fun f => eq_ratCast f _
  exact h (((GroundTheory.Automorphic.GodementSection.adeleAt v).comp Adele2.finRingHom).comp (algebraMap ℚ 𝔸[ℚ]))

end GlobalTheory.CompanionTheory.FexTheta
