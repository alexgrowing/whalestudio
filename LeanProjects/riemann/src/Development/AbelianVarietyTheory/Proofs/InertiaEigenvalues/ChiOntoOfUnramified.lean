import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramCyc

open PowerSeries in

theorem _root_.GlobalTheory.UnramCyc.chi_onto_of_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (K : _root_.Formalism.BasicNotions.Loc.FinExt l),
    K.1 ≤ _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l → ∀ c : ℤ_[l]ˣ, ∃ g ∈ _root_.Formalism.BasicNotions.Loc.GK K, (P.χQ g : ℚ_[l]) = ((c : ℤ_[l]) : ℚ_[l]) := by
  intro l _ P K hK c
  have hnorm : ‖((c : ℤ_[l]) : ℚ_[l])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units c
  obtain ⟨g, hg, hgc⟩ := _root_.GlobalTheory.Cyc.exists_chi_eq K P.χQ P.χQ_cyc _ hnorm
  have hK0 : _root_.Formalism.BasicNotions.Loc.K0 K = K.1 := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact inf_eq_left.mpr hK
  refine ⟨g, ?_, hgc⟩
  unfold _root_.Formalism.BasicNotions.Loc.GK
  rw [← hK0]
  exact hg

end GlobalTheory.UnramCyc
