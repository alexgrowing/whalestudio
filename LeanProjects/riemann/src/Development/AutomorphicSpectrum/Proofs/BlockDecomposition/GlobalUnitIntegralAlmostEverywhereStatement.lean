import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitIntegralAlmostEverywhere
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_unit_integral_almost_everywhere : ∀ (K : Type) [Field K] [NumberField K] (κ : Kˣ), ∃ S : Finset Pl, ∀ v ∉ S, ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal →
  ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧ (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] := by
  first | exact @GlobalTheory.CompanionTheory.KUnit.unit_almost_everywhere | exact GlobalTheory.CompanionTheory.KUnit.unit_almost_everywhere | (intros; apply GlobalTheory.CompanionTheory.KUnit.unit_almost_everywhere <;> assumption)
