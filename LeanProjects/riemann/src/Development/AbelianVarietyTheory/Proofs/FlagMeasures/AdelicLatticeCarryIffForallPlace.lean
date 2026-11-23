import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlaceStatement

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Carry

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in

theorem prVec_mulVec (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F)) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (y.1 *ᵥ x) = (bc (prV (E := E) v) y).1 *ᵥ prVec v x := by
  funext i
  exact RingHom.map_mulVec (prV (E := E) v) y.1 x i

omit [NumberField E] in
theorem prVec_single_self (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec v (fun i => Formalism.UG.P.afsplitIE v (x i)) = x := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE v (x i)

omit [NumberField E] in
theorem prVec_single_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : Fin n → E ⊗[F] v.adicCompletion F) :
    prVec w (fun i => Formalism.UG.P.afsplitIE v (x i)) = 0 := by
  funext i
  exact Formalism.UG.P.afsplit_prV_IE_ne v w h (x i)

theorem carry_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  intro F E _ _ _ _ _ n L M hL hM y
  have lgL := GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n L hL
  have lgM := GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n M hM
  constructor
  · intro h v x
    have h1 := h (fun i => Formalism.UG.P.afsplitIE v (x i))
    rw [lgL, lgM] at h1
    constructor
    · intro hx
      have h2 := h1.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw]; exact Submodule.zero_mem _) v
      rwa [prVec_mulVec, prVec_single_self] at h2
    · intro hx
      have h2 := h1.2 (fun w => by
        rw [prVec_mulVec]
        by_cases hw : w = v
        · subst hw; rw [prVec_single_self]; exact hx
        · rw [prVec_single_ne v w hw, Matrix.mulVec_zero]; exact Submodule.zero_mem _) v
      rwa [prVec_single_self] at h2
  · intro h x
    rw [lgL, lgM]
    refine forall_congr' fun v => ?_
    rw [prVec_mulVec]
    exact h v _

end GlobalTheory.St.G.Carry
