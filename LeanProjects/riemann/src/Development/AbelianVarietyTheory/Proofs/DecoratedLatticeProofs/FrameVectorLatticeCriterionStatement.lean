import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameVectorLatticeCriterion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCore
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_vector_lattice_criterion : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (c : ℕ) (hc : 0 + c = G.s + 1) (L : Lat (d.st 0).V), Formalism.L2.DIV.IsFrame (d.st 0).β (d.st 0).Λ → Moves (d.st 0).V (d.t 0) (d.st 0).Λ L (· = G.q.v) → ∀ y : GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin c → G.k, (fun r => G.q.sec (((G.FY 0 c hc).β *ᵥ y) r)) ∈ latV (d.st 0).V L (· = G.q.v) ↔ (∀ a, y (Sum.inl a) ∈ 𝒪[G.k]) ∧ ∀ i : Fin c, ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k] := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.latV_normalFrame_zero | exact GlobalTheory.Core.Mi.LatMatch.latV_normalFrame_zero | (intros; apply GlobalTheory.Core.Mi.LatMatch.latV_normalFrame_zero <;> assumption)
