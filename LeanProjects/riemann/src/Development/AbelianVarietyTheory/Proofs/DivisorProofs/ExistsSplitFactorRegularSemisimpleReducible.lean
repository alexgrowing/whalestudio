import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.SplitFactor

theorem exists_split_factor : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E), 0 < n → IsRegSS (γ : Matrix (Fin n) (Fin n) E) → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseRank σ J γ → ¬ Irreducible (γ : Matrix (Fin n) (Fin n) E).charpoly → ¬ IsNonFieldAniso σ J (γ : Matrix (Fin n) (Fin n) E) → ∃ (k : ℕ) (K : Fin k → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Algebra F (K i)), Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) ∧ ∃ i, ¬ IsField (K i ⊗[F] E) := by
  intro F E _ _ _ n σ J γ hn hreg hAlg hRank hirr hnf
  obtain ⟨k, K, hK, hKA, ⟨e⟩⟩ := hRank.1
  refine ⟨k, K, hK, hKA, ⟨e⟩, ?_⟩
  by_contra hall
  push_neg at hall
  have h2 := hRank.2 k K ⟨e⟩
  have hk1 : 1 ≤ k := h2.2.1 ⟨⟨0, hn⟩⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk' : k = 1 := by omega
    have hfield : IsField (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix (Fin n) (Fin n) E)) := h2.2.2.2 ⟨hk', hall⟩
    obtain ⟨φ, -⟩ := hAlg.1
    have hfA : IsField (AdjoinRoot (γ : Matrix (Fin n) (Fin n) E).charpoly) :=
      φ.toMulEquiv.isField hfield
    have hmax : (Ideal.span {(γ : Matrix (Fin n) (Fin n) E).charpoly}).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hfA
    have hne : (γ : Matrix (Fin n) (Fin n) E).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hprime : Prime (γ : Matrix (Fin n) (Fin n) E).charpoly :=
      (Ideal.span_singleton_prime hne).1 hmax.isPrime
    exact hirr hprime.irreducible
  · exact hnf ⟨hreg, k, K, hK, hKA, ⟨e⟩, hk, hall⟩

end GlobalTheory.SplitFactor
