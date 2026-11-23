import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingNorm_det_splitPlace_lattice_intersection : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), IsSelfDualAt σ J L v → ∀ (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)), IsSplitBasis τ L β → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∀ d : Fin n → (Fv F v)ˣ, IsElemDiv (splitEquivIn h hJ τ β g) d → absEv F E v (Matrix.GeneralLinearGroup.det α) = ∏ i, min ‖(d i : Fv F v)‖₊ ‖(d i : Fv F v)‖₊⁻¹ := by
  first | exact @GlobalTheory.SplitInterDet.absEv_det_split | exact GlobalTheory.SplitInterDet.absEv_det_split | (intros; apply GlobalTheory.SplitInterDet.absEv_det_split <;> assumption)
