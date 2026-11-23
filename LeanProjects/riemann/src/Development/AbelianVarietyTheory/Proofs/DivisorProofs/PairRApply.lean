import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBound

noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.SchrPairing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def pairR {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (b : V) : V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => P y b
      map_add' := fun x x' => hP.addL x x' b
      map_smul' := fun c x => by simpa using hP.smulL c x b }

theorem pairR_apply {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (b y : V) : pairR hP b y = P y b := rfl

def schrSch {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (w : V × V) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP w.2) y + -(P w.1 w.2 / 2)))).comp
    (SchwartzMap.compSubConstCLM ℂ (-w.1))

theorem coe_schrSch {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (w : V × V) (f : 𝓢(V, ℂ)) :
    ⇑(schrSch hP w f) = GlobalTheory.ArchUniq.schrF P w ⇑f := by
  funext y
  rw [schrSch, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase _ _),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, GlobalTheory.ArchUniq.schrF, GlobalTheory.Published.Metaplectic.eChar_apply,
    sub_neg_eq_add, ContinuousLinearMap.neg_apply, pairR_apply]
  congr 1
  congr 1
  push_cast
  ring

end GlobalTheory.SchrPairing
