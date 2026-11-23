import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

abbrev Idx (n d : ℕ) : Type := Fin n ⊕ (Fin d × {p : Fin n × Fin n // p.1 < p.2})

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hCo (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : HermR R σ n) : Idx n d → R :=
  Sum.elim
    (fun i => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    (fun q => (Algebra.TensorProduct.basis R b).repr
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) q.2.1.1 q.2.1.2) q.1)

def coordForm (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) : Matrix (Idx n d) (Idx n d) F :=
  Matrix.fromBlocks 1 0 0
    (Matrix.blockDiagonal fun _ : {p : Fin n × Fin n // p.1 < p.2} =>
      Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l)))

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
