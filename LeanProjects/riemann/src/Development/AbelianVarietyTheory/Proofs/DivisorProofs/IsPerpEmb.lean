import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT)

namespace GlobalTheory.LeviFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def gram {d : ℕ} (B : Matrix (Fin n) (Fin d) E) : Matrix (Fin d) (Fin d) E := cT (σ : E →+* E) B * J * B

def IsPerpEmb (X Y : Matrix (Fin n) (Fin r) E) (k : Fin r) {d : ℕ} (B : Matrix (Fin n) (Fin d) E)
    (ι : GAd σ (gram σ J B) →* GAd σ J) : Prop :=
  d + 2 * (k.val + 1) = n ∧ cT (σ : E →+* E) (GlobalTheory.StdPar.initCols X k) * J * B = 0 ∧
    cT (σ : E →+* E) (GlobalTheory.StdPar.initCols Y k) * J * B = 0 ∧ IsHermND σ (gram σ J B) ∧
    ∀ h, (matHom _ σ J (ι h)).1 =
      1 + adMat F B * ((matHom _ σ (gram σ J B) h).1 - 1) * adMat F ((gram σ J B)⁻¹ * cT (σ : E →+* E) B * J)

end GlobalTheory.LeviFin

end
