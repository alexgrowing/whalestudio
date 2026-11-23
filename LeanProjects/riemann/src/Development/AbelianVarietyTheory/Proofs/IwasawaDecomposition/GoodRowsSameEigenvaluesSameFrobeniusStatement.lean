import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodRowsSameEigenvaluesSameFrobenius
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_rows_same_eigenvalues_same_frobenius : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (Sb : Finset (PlE D.host)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0), GlobalTheory.TwInputs.EigTrue D cf Rw Sb eig → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ σ' : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.what₂.isot j σ' ≠ ⊥ → D.nd.goodRow σ' → ∀ P : PlE D.host, IsSplitPl D.host P → P ∉ Sb → (∀ k, 1 ≤ k → k ≤ D.R.r → eig j σ' k P = eig j σ k P) → D.naut.frobEig (Rw.locR σ' P) = D.naut.frobEig (Rw.locR σ P) := by
  first | exact @GlobalTheory.FrobSame.frobEig_eq_of_eig_eq | exact GlobalTheory.FrobSame.frobEig_eq_of_eig_eq | (intros; apply GlobalTheory.FrobSame.frobEig_eq_of_eig_eq <;> assumption)
