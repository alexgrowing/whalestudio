import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEquationBaseChangeAlgHom
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryEquation_baseChange_algHom : ∀ {F E R K : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] K) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J → Formalism.UG.cT (sigR K σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) * JR K J * g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = JR K J := by
  first | exact @GlobalTheory.unitaryEq_baseChange | exact GlobalTheory.unitaryEq_baseChange | (intros; apply GlobalTheory.unitaryEq_baseChange <;> assumption)
