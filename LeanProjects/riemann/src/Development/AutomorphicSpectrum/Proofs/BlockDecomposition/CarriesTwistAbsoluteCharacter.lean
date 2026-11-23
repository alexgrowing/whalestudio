import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_absFn_tw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z z' : ℂ) : Carries (absFn N (z' - z)) (tw U z) (tw U z') := by
  rintro φ ⟨ψ, hψ, rfl⟩
  refine ⟨mulChi N (GlobalTheory.CuspRep.Model.absC E z') ψ, ⟨ψ, hψ, rfl⟩, fun x => ?_⟩
  have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
      Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
  simp only [LinearEquiv.coe_coe, mulChi_apply, absFn]
  rw [e z', e (z' - z), e z, mul_left_comm, ← Complex.exp_add, ← add_mul, sub_add_cancel]

end GlobalTheory.CompanionTheory.LimV

end
