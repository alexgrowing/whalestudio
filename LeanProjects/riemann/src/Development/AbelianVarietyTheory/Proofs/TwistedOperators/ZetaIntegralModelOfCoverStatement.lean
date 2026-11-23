import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIntegralModelOfCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIntegral_model_of_cover : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (c : ℚ) (m : ℤ) (br : Bool) (e : Ix p q ≃ Fin W.rank) (e' : Ix r s ≃ Fin V.rank) (u : kfin N τ → (X.ds p q lam).HK.V) (K : ℝ), ARi X lam lam' → (∀ v, UnitHW (X.ds p q lam) (blattner lam) v → Integrable (eFun (X.ds p q lam) v) (X.grp p q).haar) → KTie (X.ds p q lam) N τ lam c br false e u → SignCompat (M.ε τ) e' → (m : ℚ) = 2 * c → Coef (X.fock p q r s) B pt ip κ (phiFr (N.fr τ) br e) m K → (∀ Φ, IsJoint M τ A pt N B Φ → CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') (κ Φ)) → ZetaLaw M τ A pt N B ip := by
  first | exact @GlobalTheory.ArchRec.ZetaTransfer.zetaLaw_of_cover | exact GlobalTheory.ArchRec.ZetaTransfer.zetaLaw_of_cover | (intros; apply GlobalTheory.ArchRec.ZetaTransfer.zetaLaw_of_cover <;> assumption)
