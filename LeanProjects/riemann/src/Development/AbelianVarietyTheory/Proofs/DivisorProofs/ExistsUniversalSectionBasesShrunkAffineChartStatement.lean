import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (w : M.Z), IsAffineOpen U₀ → w ∈ U₀ → ∀ (P : PolAV (Sp (M.ringOn U₀))) (N : ℕ), 1 ≤ N → ∃ (U : M.Z.Opens) (h : M.ringOn U₀ ≤ M.ringOn U) (P' : PolAV (Sp (M.ringOn U))) (φ : P'.A.left ⟶ P.A.left), U ≤ U₀ ∧ IsAffineOpen U ∧ w ∈ U ∧ IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso P'.L (P.L.pull φ) ∧ P'.g = P.g ∧ (∃ th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (M.ringOn U)))), GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) ∧ ∃ b : Fin (N ^ P'.g) → SecM P'.A P'.L (N : ℕ) (baseOver (Sp (M.ringOn U))), GlobalTheory.ThetaReal.UnivBasis P' (N : ℕ) b := by
  first | exact @GlobalTheory.Poinc.exists_univBasis_affineChart | exact GlobalTheory.Poinc.exists_univBasis_affineChart | (intros; apply GlobalTheory.Poinc.exists_univBasis_affineChart <;> assumption)
