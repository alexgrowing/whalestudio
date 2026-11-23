import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOver
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
theorem _root_.GlobalTheory.T.finiteMatrix_apply_eq_one_at_places_over_of_oneAt : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (HeightOneSpectrum.under (𝓞 D.host.F) P) - algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) P)) k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v ((ι (a ⊗ₜ[D.host.F] 1)) P - algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → ∀ (V : HSp D) (l : ℕ) (z : GA D V), OneAt V l z → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  first | exact @GlobalTheory.LevelSeries.FinOneAt.oneAt_fin_eq_one | exact GlobalTheory.LevelSeries.FinOneAt.oneAt_fin_eq_one | (intros; apply GlobalTheory.LevelSeries.FinOneAt.oneAt_fin_eq_one <;> assumption)
