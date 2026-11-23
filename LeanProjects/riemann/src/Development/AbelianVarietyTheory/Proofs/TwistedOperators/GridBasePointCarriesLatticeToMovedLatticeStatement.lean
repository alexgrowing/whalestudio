import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointCarriesLatticeToMovedLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridBasePoint_carries_lattice_to_movedLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → ∀ (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (t : T), t ∈ U → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ b : Pts G, IsBase t S.B b → ∀ w ∈ locPl G t, ∀ p : GlobalTheory.FinPl.SplitPt D (Kw w), Formalism.L2.NTheta.IsIdemAt p.e w → (∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a))) → ∀ x : Fin (G.V (.grid D.R.m 0)).rank → Kw w, ((fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = p.v) ↔ (fun i => p.sec (((Formalism.L2.Theta.mt _ (b 0)).map p.pr *ᵥ x) i)) ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = p.v)) := by
  first | exact @GlobalTheory.BaseMoveAt.lat_moves_at_place | exact GlobalTheory.BaseMoveAt.lat_moves_at_place | (intros; apply GlobalTheory.BaseMoveAt.lat_moves_at_place <;> assumption)
