import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_tw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ)
    (U U' : Submodule ℂ (Sm E N)) (z : ℂ) (h : Carries e U U') : Carries e (tw U z) (tw U' z) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', hx⟩ := h ψ hψ
  refine ⟨mulChi N (Model.absC E z) ψ', ⟨ψ', hψ', rfl⟩, fun x => ?_⟩
  simp only [LinearEquiv.coe_coe, mulChi_apply, hx, mul_assoc]

end GlobalTheory.CompanionTheory.LimV

end
