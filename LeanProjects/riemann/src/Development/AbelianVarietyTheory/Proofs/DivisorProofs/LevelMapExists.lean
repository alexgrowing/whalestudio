import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpFrame.LevelMap

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ}

theorem grpA_mul (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) (g h : ι → GL (Fin N) O) :
    grpA O N lam (g * h) = grpA O N lam g * grpA O N lam h := by
  apply Subtype.ext
  show grp O N lam (g * h) = grp O N lam g * grp O N lam h
  unfold grp
  exact map_mul _ g h

theorem grpA_one (O : Type) [CommRing O] (lam : ι → ℕ → ℕ) :
    grpA O N lam 1 = 1 := by
  apply Subtype.ext
  show grp O N lam 1 = 1
  unfold grp
  exact map_one _

def jK (F : Frame l ι N) (lam : ι → ℕ → ℕ) : F.K →* alg F.O N lam where
  toFun κ := (F.chi κ : F.O) • grpA F.O N lam (F.kap κ)
  map_one' := by simp [grpA_one]
  map_mul' a b := by
    rw [map_mul, map_mul, grpA_mul, Units.val_mul, smul_mul_smul_comm]

end GlobalTheory.ExpFrame.LevelMap

theorem GlobalTheory.ExpFrame.levelMap_exists : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), ∃ (jK : F.K →* alg F.O N lam), F.IsJ lam jK := by
  intro l _ ι _ _ N F lam
  exact ⟨GlobalTheory.ExpFrame.LevelMap.jK F lam, fun κ => rfl⟩

end
