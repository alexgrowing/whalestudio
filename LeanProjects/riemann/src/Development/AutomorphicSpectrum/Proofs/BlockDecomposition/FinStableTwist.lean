import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem finStable_tw {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ) (h : FinStable U) : FinStable (tw U z) := by
  rintro g _ ⟨ψ, hψ, rfl⟩
  exact ⟨_, U.add_mem (U.smul_mem _ (h g ψ hψ)) (U.smul_mem _ hψ), (act_mulChi _ (.fin g) ψ).symm⟩

end GlobalTheory.CompanionTheory.LimV
