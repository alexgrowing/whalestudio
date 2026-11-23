import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll
import Formalism.PeriodIntegrals.PhMeasCore
import Formalism.RealPlaceAnalysis.Complexify

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

theorem unitary_group_admissible (n : ℕ) (ε : Fin n → Bool) : AdmUJ ε := admissible_of_iwasawa (iwasawa_decomposition_unitary_group n ε)

theorem kFin_smooth (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (v : H) (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v :=
  smooth_of_adm (unitary_group_admissible n ε) garding_finite_smooth_vectors hσ hirr hv

theorem kFin_mem_smoothVecs (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (v : H) (hv : IsKFin ε σ v) :
    v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ :=
  kFin_smooth n ε H σ hσ hirr v hv

end CompanionTheory.D.gk.admitted
