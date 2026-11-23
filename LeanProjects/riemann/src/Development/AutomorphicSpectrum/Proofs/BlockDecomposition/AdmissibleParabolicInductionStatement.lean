import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_parabolic_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n) (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)), GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) := by
  first | exact @GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr | exact GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr | (intros; apply GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr <;> assumption)
