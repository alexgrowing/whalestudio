import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]

def ptrB (M : Meas r F E) (ψ : AddChar F ℂ) (f : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b, f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1) ∂(Measure.pi fun _ : Fin r => M.μF)

def rowMap (g : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) : Gl r F :=
  (Y.1, fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 0, Y.2.2.2)

def rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (Y : Gl r F) : ℂ := h (rowMap g Y)

def weil (M : Meas r F E) (ψ : AddChar F ℂ) (g : SpecialLinearGroup (Fin 2) F) (f : Gl r F → ℂ) : Gl r F → ℂ :=
  ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct g (ptrB M ψ f))))

def negB (f : Gl r F → ℂ) (Y : Gl r F) : ℂ := f (Y.1, -Y.2.1, Y.2.2.1, Y.2.2.2)

end GlobalTheory.JR.WeilMix
