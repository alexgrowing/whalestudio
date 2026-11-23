import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXLocSB

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter Matrix
open scoped TensorProduct

def AlgWitt : Prop :=
  ∀ (S : Type) [CommRing S] (s : S →+* S) (O : Subring S), (∀ z, s (s z) = z) → (∀ z ∈ O, s z ∈ O) →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) S), Formalism.UG.IsHerm s J → J' * J = 1 →
    (∀ i j, J i j ∈ O) → (∀ i j, J' i j ∈ O) →
    ∀ (a : ℕ) (β β' : Fin a → S), (∀ i, β i ∈ O) → (∀ i, β' i ∈ O) → (∀ i, β i * β' i = 1) →
    (∀ i, ∀ t ∈ O, ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (β i - s lam * t) * c' = 1) →
    ∀ (x y : Fin a → Fin n → S), (∀ i k, x i k ∈ O) → (∀ i k, y i k ∈ O) →
    (∀ i j, Formalism.UG.hform s J (x i) (x j) = if i = j then β i else 0) →
    (∀ i j, Formalism.UG.hform s J (y i) (y j) = if i = j then β i else 0) →
    ∃ g : GL (Fin n) S, g ∈ Formalism.UG.UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i

def HermDiag : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ z, σ (σ z) = z) → (2 : K) ≠ 0 →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm σ J →
    ∀ (a : ℕ) (X0 : Fin a → Fin n → K),
    (Matrix.of fun i j => Formalism.UG.hform σ J (X0 i) (X0 j)).det ≠ 0 →
    ∃ P Q : Matrix (Fin a) (Fin a) K, Q * P = 1 ∧
      (∀ i j, i ≠ j → Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P j l • X0 l) = 0) ∧
      ∀ i, Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P i l • X0 l) ≠ 0

def LamAE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ δ : E, σ δ = δ → δ ≠ 0 →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ t ∈ OEv (E := E) v,
      ∃ lam ∈ OEv (E := E) v, lam * sigR (Fv F v) σ lam = 1 ∧
        ∃ c' ∈ OEv (E := E) v, (inclR (Fv F v) δ - sigR (Fv F v) σ lam * t) * c' = 1

end Formalism.L2.SG.Pf.NcX.IntWittPf
