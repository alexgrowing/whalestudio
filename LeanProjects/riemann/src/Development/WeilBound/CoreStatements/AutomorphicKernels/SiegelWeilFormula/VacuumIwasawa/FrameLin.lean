import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFramesPreserveNormSqSumStatement

noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {m : ℕ}

theorem norm_frame_eq (hm : 1 ≤ m) (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ)
    (hζ : ζ = 1 ∨ ζ = Complex.I) (hζ' : ζ' = 1 ∨ ζ' = Complex.I)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (h' : ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1)
    (v : Fin m → ℂ) : ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 :=
  GlobalTheory.T.unitary_frames_preserve_norm_sq_sum m hm J fr fr' ζ ζ' s s' hζ hζ' h h' v

end PositivityTheory.SiegelWeilFormula.Avac

end
