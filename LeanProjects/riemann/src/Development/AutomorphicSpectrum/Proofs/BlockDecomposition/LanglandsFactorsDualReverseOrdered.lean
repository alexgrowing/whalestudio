import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.DualForms

theorem exists_revOrdered_dual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k →
    ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL k), LFactors 𝔪 x →
      ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  intro k _ _ _ _ hA hD 𝔪 h x hx
  obtain ⟨Δ, ⟨-, hord⟩, hL⟩ := hx
  refine ⟨fun i => segDual (Δ i), fun i j hij hp => hord i j hij ((GlobalTheory.T.segment_dual_precedes_iff hA _ _).1 hp), fun i => ?_⟩
  rw [GlobalTheory.CompanionTheory.Zcore.dualCl_eq_of hA (x i)]
  exact (hD (Δ i) (x i).rep (hL i)).of_equiv (IrrGL.equivOf _ _ _)

end GlobalTheory.CompanionTheory.DualForms
