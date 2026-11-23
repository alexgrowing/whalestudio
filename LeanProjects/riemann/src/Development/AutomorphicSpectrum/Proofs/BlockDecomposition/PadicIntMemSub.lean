import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCZp

theorem padicInt_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) (z : ℤ_[l]) :
    Lat.pk l k (algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))) ∈
      Lat.sub (Lat.fk l k) (xi0 l) l M := by
  have h1 : algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z) :=
    ((algClToBdR l).commutes (z : ℚ_[l])).trans
      (IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l z)
  rw [h1]
  exact Subring.subset_closure (Or.inl ⟨IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z, rfl⟩)

end GlobalTheory.CompanionTheory.LatCZp
