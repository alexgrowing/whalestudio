import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def SDarb_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd ∧ ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : Fin m × Fin n × Fin 2 → F,
      dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))
def SEv_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∀ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd →
    ev0 (F := F) (Fin m × Fin n × Fin 2) ∈ (adeleClass F).adm (Fin m × Fin n × Fin 2) ∧
    (∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2),
      ev0 _ (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ) = ev0 _ Φ) ∧
    ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2), HasSum (fun y : Matrix (Fin m) (Fin n) E =>
      ev0 _ (dd.rho B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
