import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker

namespace GlobalTheory.LocLanglands

def lowUnip {R : Type} [CommRing R] {m r n : ℕ} (hn : m + r = n) (y : Matrix (Fin r) (Fin m) R) : GL (Fin n) R where
  val := Matrix.reindex (stdSum hn) (stdSum hn) (fromBlocks 1 0 y 1)
  inv := Matrix.reindex (stdSum hn) (stdSum hn) (fromBlocks 1 0 (-y) 1)
  val_inv := by simp [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  inv_val := by simp [Matrix.submatrix_mul_equiv, fromBlocks_multiply]

def padRow {R : Type} [CommRing R] {j m : ℕ} (x : Fin j → Fin m → R) : Matrix (Fin (j + 1)) (Fin m) R :=
  Matrix.of (Fin.snoc (α := fun _ => Fin m → R) x 0)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSelfDualFor [MeasurableSpace k] (ψ : AddChar k Circle) (μ : Measure k) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ c : kˣ, HasConductor ψ c ∧
    μ {x | valuation k x ≤ 1} * μ {x | valuation k x ≤ valuation k (c : k)} = 1

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n m : ℕ}

def HasPairGamma (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin n) k) V)
    (τ : Representation ℂ (GL (Fin m) k) V') (e : ℂ) : Prop :=
  ∀ (j : ℕ) (hn : m + (j + 1) = n) [MeasurableSpace k] [BorelSpace k] (μ : Measure k), IsSelfDualFor ψ μ →
    ∀ ω : kˣ →* ℂˣ, HasCentralChar τ ω →
    ∀ (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V'), IsFunctional ψ π l → IsFunctional ψ⁻¹ τ l' →
      ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I → ∀ (v : V) (v' : V'),
        I (fun g => (∫ x : Fin j → Fin m → k, l (π (tilde (emb₂ k (stdSum hn) (g, 1) * lowUnip hn (padRow x) *
              emb₂ k (stdSum hn) (1, longElt (j + 1) k))) v) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) *
            l' (τ (tilde g) v') * (absPow k (-(j : ℂ) / 2) (GeneralLinearGroup.det g) : ℂ)) =
          (ω (-1) : ℂ) ^ (n - 1) * e *
            I (fun g => l (π (emb₂ k (stdSum hn) (g, 1)) v) * l' (τ g v') *
              (absPow k (-(j : ℂ) / 2) (GeneralLinearGroup.det g) : ℂ))

end GlobalTheory.LocLanglands

end
