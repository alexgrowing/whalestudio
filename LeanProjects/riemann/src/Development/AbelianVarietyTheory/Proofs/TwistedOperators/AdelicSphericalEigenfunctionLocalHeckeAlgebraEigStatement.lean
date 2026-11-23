import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicSphericalEigenfunctionLocalHeckeAlgebraEig
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSphericalEigenfunction_local_heckeAlgebra_eigen : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  first | exact @GlobalTheory.FinZeta.eigen_heckeAlg | exact GlobalTheory.FinZeta.eigen_heckeAlg | (intros; apply GlobalTheory.FinZeta.eigen_heckeAlg <;> assumption)
