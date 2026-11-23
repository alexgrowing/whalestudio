import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_dualBasis_embeddedLattice : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  first | exact @GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat | exact GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat | (intros; apply GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat <;> assumption)
