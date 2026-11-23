import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HeisenbergCoordinatesMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModTop

noncomputable section

namespace PI.VolSemiDirect.W.Md

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section Homeo

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (h2 : (2 : E) ≠ 0)

theorem continuous_wv_phiW :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => wv (phiW hσσ hJ hP n) :=
  continuous_phiW_raw R σ J P T

theorem continuous_phiW : Continuous fun n : FrameUnipotentSubgroup R σ J P => phiW hσσ hJ hP n :=
  continuous_pi fun b => continuous_induced_rng.2
    ((continuous_apply b).comp (continuous_wv_phiW hσσ hJ hP))

theorem continuous_phiSv : Continuous fun n : FrameUnipotentSubgroup R σ J P => phiSv hσσ hJ hP n :=
  continuous_gram_add R σ J (half F E R) (continuous_wv_phiW hσσ hJ hP)
    (continuous_phiS_raw R σ J P)

theorem continuous_phiS : Continuous fun n : FrameUnipotentSubgroup R σ J P => phiS hσσ hJ hP h2 n :=
  continuous_induced_rng.2 (continuous_phiSv hσσ hJ hP)

theorem continuous_nG :
    Continuous fun p : (Fin r → Wsub R σ J P) × Sk R σ r => nG hσσ hJ hP h2 p.1 p.2 := by
  apply continuous_into_HA hJ
  have hw : Continuous fun p : (Fin r → Wsub R σ J P) × Sk R σ r => wv p.1 :=
    continuous_pi fun a => continuous_subtype_val.comp ((continuous_apply a).comp continuous_fst)
  have hc : Continuous fun p : (Fin r → Wsub R σ J P) × Sk R σ r =>
      (p.2 : Fin r → Fin r → R ⊗[F] E) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_toMatrix'_L R σ J P T hw (continuous_gram_shift R σ J (half F E R) hw hc)

def coordHomeo : FrameUnipotentSubgroup R σ J P ≃ₜ ((Fin r → Wsub R σ J P) × Sk R σ r) where
  toEquiv := coordEquiv hσσ hJ hP h2
  continuous_toFun :=
    (continuous_phiW hσσ hJ hP).prodMk (continuous_phiS hσσ hJ hP h2)
  continuous_invFun := continuous_induced_rng.2 (continuous_nG hσσ hJ hP h2)

end Homeo

end PI.VolSemiDirect.W.Md
