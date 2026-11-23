import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedArchimedeanGlExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_archimedean_gl_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ w : InfinitePlace F, ∃ g : GL (Fin (dim σ J X Y)) (w.Completion ⊗[F] E),
      (∃ ε : Fin (dim σ J X Y) → Bool, Formalism.UG.cT (sigR _ σ) g.1 * JR w.Completion (J0 σ J X Y) * g.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧
      (∃ c : Fin r → w.Completion ⊗[F] E, Formalism.UG.cT (sigR _ σ) (g⁻¹).1 * (g⁻¹).1 * (X0 σ J X Y).map (inclR (F := F) w.Completion) =
        (JR w.Completion (J0 σ J X Y) * (Y0 σ J X Y).map (inclR (F := F) w.Completion) : Matrix _ _ (w.Completion ⊗[F] E)) * Matrix.diagonal c) ∧
      Formalism.UG.cT (sigR _ σ) (g⁻¹).1 * (g⁻¹).1 = Formalism.UG.cT (sigR _ σ) ((P σ J X Y).map (inclR (F := F) w.Completion)) *
        (Formalism.UG.cT (sigR _ σ) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1) * (P σ J X Y).map (inclR (F := F) w.Completion) := by
  first | exact @GlobalTheory.EisRestrictInf.restrict_inf | exact GlobalTheory.EisRestrictInf.restrict_inf | (intros; apply GlobalTheory.EisRestrictInf.restrict_inf <;> assumption)
