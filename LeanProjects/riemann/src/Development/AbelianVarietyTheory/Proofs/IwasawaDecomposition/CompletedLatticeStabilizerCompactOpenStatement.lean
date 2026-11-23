import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_stabilizer_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (Af F) σ J h : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (Af F) σ J)) ∧ IsCompact (K : Set (HA (Af F) σ J)) := by
  first | exact @GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | exact GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | (intros; apply GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab <;> assumption)
