import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification

noncomputable section

open MeasureTheory Matrix Finset Formalism.REAL GlobalTheory.FlagMeas GlobalTheory.RealInd

namespace GlobalTheory.RealInd.Stages

variable {n a b : ℕ} {ε : Fin n → Bool}

def restr {U : Type} [Zero U] (M : Subgroup (UJ ε)) (F : UJ ε → U) (g : UJ ε) : UJ ε → U :=
  (M : Set (UJ ε)).indicator fun m => F (m * g)

open Classical in

def stageFun {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (M : Subgroup (UJ ε))
    (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (F : UJ ε → U) (g : UJ ε) : V :=
  if h : restr M F g ∈ Fsp then ι ⟨_, h⟩ else 0

def blockMean (j : Fin a → ℕ) (β : Fin b → Fin a) (y : Fin b → ℝ) (i : Fin a) : ℝ :=
  (∑ l with β l = i, y l) / j i

def stageS (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ) : Fin b → ℂ :=
  fun l => s (β l) + Complex.I * ((y l - blockMean j β y (β l) : ℝ) : ℂ)

theorem restr_of_mem {U : Type} [Zero U] {M : Subgroup (UJ ε)} (F : UJ ε → U) (g : UJ ε) {m : UJ ε} (hm : m ∈ M) :
    restr M F g m = F (m * g) := Set.indicator_of_mem hm _

theorem restr_of_not_mem {U : Type} [Zero U] {M : Subgroup (UJ ε)} (F : UJ ε → U) (g : UJ ε) {m : UJ ε}
    (hm : m ∉ M) : restr M F g m = 0 := Set.indicator_of_notMem hm _

theorem stageFun_of_mem {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    {M : Subgroup (UJ ε)} {Fsp : Submodule ℂ (UJ ε → U)} (ι : Fsp →ₗ[ℂ] V) {F : UJ ε → U} {g : UJ ε}
    (h : restr M F g ∈ Fsp) : stageFun M Fsp ι F g = ι ⟨_, h⟩ := dif_pos h

end GlobalTheory.RealInd.Stages

end
