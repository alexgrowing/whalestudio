import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classSet_hermitianUnitary_openLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ K : Subgroup (HA (Af F) σ J), IsOpen (K : Set (HA (Af F) σ J)) → ∃ S : Finset (HA (Af F) σ J), ∀ g : HA (Af F) σ J, ∃ γ : HFinIn (Af F) σ J, ∃ s ∈ S, ∃ k ∈ K, g = γ • (s * k) := by
  first | exact @GlobalTheory.Mem.ClassFinite.exists_finset_classes | exact GlobalTheory.Mem.ClassFinite.exists_finset_classes | (intros; apply GlobalTheory.Mem.ClassFinite.exists_finset_classes <;> assumption)
