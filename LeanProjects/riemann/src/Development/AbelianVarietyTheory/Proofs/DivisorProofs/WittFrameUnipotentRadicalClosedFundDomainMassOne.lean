import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem unipRad_frame_closed_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have e : X = X.submatrix id (Fin.castLE (le_refl (r + 1))) := by
    ext i j
    rfl
  have hC : GlobalTheory.UAut.IsIsoCols σ J X := e ▸ GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hC
  exact ⟨GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) X 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma h) hC _,
    GlobalTheory.UAut.exists_mass_one (GlobalTheory.UAut.cocompact_unipRad h hJ hC)⟩

end GlobalTheory.ResidueEisenstein
