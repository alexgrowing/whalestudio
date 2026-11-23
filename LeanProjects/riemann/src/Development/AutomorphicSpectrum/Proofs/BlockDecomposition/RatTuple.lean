import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SW.Core
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def InNOh {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) (x : Af F ⊗[F] E) : Prop :=
  ∀ k, ∃ y ∈ Oh F, (Algebra.TensorProduct.basis (Af F) b).repr x k = (N : Af F) * y

def latN {d : ℕ} (b : Module.Basis (Fin d) F E) (n M N : ℕ) :
    AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) where
  carrier := {X | ∀ a i, InNOh b N (X a i)}
  zero_mem' := fun a i k => ⟨0, fun v => zero_mem _, by simp⟩
  add_mem' := by
    intro X Y hX hY a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    obtain ⟨y, hy, ey⟩ := hY a i k
    refine ⟨x + y, fun v => add_mem (hx v) (hy v), ?_⟩
    simp only [Pi.add_apply, map_add, Finsupp.add_apply, ex, ey, mul_add]
  neg_mem' := by
    intro X hX a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    refine ⟨-x, fun v => neg_mem (hx v), ?_⟩
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply, ex, mul_neg]

def gram2 (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  fun a c => hR (Af F) σ J (X a) (Y c)

def phaseB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X)))

def pairB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X Y : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)))

def ratTuple [NumberField E] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : ℕ) (ρ : Fin M → Fin n → 𝓞 E) :
    Fin n → Fin M → Af F ⊗[F] E :=
  fun a j => inclR (Af F) ((s : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
