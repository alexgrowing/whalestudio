import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeCont

open NumberField
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem summable_norm_ratMat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t : {r : ℝ // 0 < r}) (a b : AdelicGLn.AdelicGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t * a :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖) := by
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ t (isCompact_singleton (x := a))
    (isCompact_singleton (x := b))
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun ξ => hbd t le_rfl a rfl b rfl ξ)

end GJGlobal

end

end GroundTheory.Automorphic
