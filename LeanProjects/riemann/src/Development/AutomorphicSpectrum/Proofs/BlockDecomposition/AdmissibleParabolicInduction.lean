import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd

namespace GlobalTheory.CompanionTheory.ProdAdm

theorem isAdmissible_multiProd_smIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n)
    (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)) :
    GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) :=
  PositivityTheory.PfBern.Props1.isAdmissible_parInd_of _ _
    (GlobalTheory.ContraProd.isAdmissible_piTensor _ _ fun i =>
      PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k (N i) (σ i).V (σ i).ρ (σ i).smooth (σ i).irred)

end GlobalTheory.CompanionTheory.ProdAdm
