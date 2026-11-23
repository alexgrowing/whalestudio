import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDenom_rationalMatrix_of_finitePart : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → ∀ (V : HSp D) (l c : ℕ) (γ : GA D V) (γ' : GL (Fin V.rank) D.host.E), GlobalTheory.Member.IsRat V γ γ' → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1).1) → GlobalTheory.StdAtPrime.Bnd l ((((l ^ c : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E)) • (Matrix.GeneralLinearGroup.map ι.toRingHom (fin V γ).1)⁻¹.1) → DenomAt l c γ' := by
  first | exact @GlobalTheory.LevelSeries.denomAt_of_isRat_of_bnd | exact GlobalTheory.LevelSeries.denomAt_of_isRat_of_bnd | (intros; apply GlobalTheory.LevelSeries.denomAt_of_isRat_of_bnd <;> assumption)
