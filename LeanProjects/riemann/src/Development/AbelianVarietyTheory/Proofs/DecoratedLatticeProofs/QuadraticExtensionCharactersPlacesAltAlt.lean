import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QVecTopStep

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → v.Is → ∀ (r : ℕ) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (G : ∀ i, QGeo v B (pl i)) (E : ∀ i, QExt (G i) χ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (S : GlobalTheory.FinPl.Pl D → Prop), Function.Injective (fun i => (G i).q.v) → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → (∀ p, S p ↔ ∃ i, (G i).q.v = p) → (∀ i, (G i).Res (E i).δ (ξ (pl i))) → (∀ i, D.R.r = D.R.k + ((G i).s + 1)) → ∀ j (h : j + 2 * 0 + 2 = D.R.m), GlobalTheory.FinPl.Moves (c.V (j + 1)) (B.b (j + 1)) (B.Λ (j + 1)) (v.N (j + 1)) S → GlobalTheory.FinPl.Moves c.T B.bT B.ΛT v.NT S → B.b (j + 1) ∈ GfC (c.V (j + 1)) → B.bT ∈ GfC c.T → IsSelfDualC _ (B.Λ (j + 1)) → IsSelfDualC _ B.ΛT → ∀ sS sT (LS : Formalism.L2.DIV.LevDat D.host.E ℂ (c.V (j + 1)).rank) χj vac (d : WO (c.V (j + 1)) c.T →₀ ℂ), LS.Pg = ∅ → LS.r = D.R.r → vac ≠ 0 → GlobalTheory.FinPl.CombAt S d → IsStepVecOf c.ψ c.θ (c.V (j + 1)) c.T sS sT (B.Λ (j + 1) : Set _) (B.ΛT : Set _) (B.β (j + 1)) B.βT LS χj Q ξ vac (comb c.ψ _ _ d vac) → ∀ χS χT om, IsWeilDatumO c.ψ (c.V (j + 1)) c.T χS χT om → ∀ g, GlobalTheory.FinPl.Vac c.ψ _ _ (B.Λ (j + 1)) B.ΛT S g → om (B.b (j + 1), B.bT) (comb c.ψ _ _ d g) = comb c.ψ _ _ (aconv (List.ofFn fun i => (E i).toAt.eT j h)) (om (B.b (j + 1), B.bT) g) :=
  fun D c v B χ _ => GlobalTheory.QVecJoin.step_top D c v B χ

end GlobalTheory.QVecTopStep
