import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeOddMapLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeEvenMapLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartKEquivariantExtensionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LowKStep

theorem map_mem_fockDeg_of_succ : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ k : ℕ, lowDegInf B G.M R.p ≤ k → ∀ S : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) S →
        (∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb (k + 1)).map R.p) →
          ∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb k).map R.p := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM k hk S hS hS1
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  ·
    intro x hx
    exact GlobalTheory.T.fock_degree_odd_map_le hKP F E σ B a a' G X om om' R Rf hM j (hS1 x hx)
  ·
    intro x hx
    have h2 := GlobalTheory.T.low_part_K_equivariant_extension hKP F E σ B a a' G X om om' R Rf hM j S hS (fun y hy => by
      have := hS1 y hy
      rw [show lowDegInf B G.M R.p + (2 * j + 1) + 1 = lowDegInf B G.M R.p + 2 * j + 2 by ring] at this
      exact GlobalTheory.T.fock_degree_even_map_le hKP F E σ B a a' G X om om' R Rf hM j this) x hx
    exact Submodule.map_mono (fockDeg_mono _ _ _ (by omega)) h2

end GlobalTheory.LowKStep
