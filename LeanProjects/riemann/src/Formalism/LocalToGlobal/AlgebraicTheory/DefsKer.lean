import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Formalism.GaussJetBounds.Statement

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (matH IsLat IsReps opU sumU taylorMv)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Col (Fields Sp HomE homAt divLat IsSdLat)
open Formalism.L2.Ker (Amb DVar VCx LamC BC AC HV alV embH volC repsOf derivAt0)
open Formalism.DworkPowerSeriesWeights (mfact)

def killIn {V : Type*} [AddCommGroup V] [Module ℂ V] (m : ℂ) (L M : AddSubgroup V) : AddSubgroup V :=
  L ⊓ M.comap ((m • LinearMap.id : V →ₗ[ℂ] V).toAddMonoidHom)

def KerIndForm : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    IsSdLat N → IsSdLat N' → A.LaHyp a b S → 0 < c → 0 < volC A.AA S N N' →
  ∀ (m₁ m₂ : ℕ), Nat.Coprime m₁ m₂ →
    (∀ y ∈ BC (X.embC A.σ₀) A.δ A.AA S N N' c, (((m₁ * m₂ : ℕ) : ℂ)) • y ∈ LamC (X.embC A.σ₀) A.δ A.AA N N') →
  ∀ S₁ S₂ : Finset (VCx X.Tau a b),
    IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (killIn (m₁ : ℂ) (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N')) S₁ →
    IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (killIn (m₂ : ℂ) (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N')) S₂ →
  ∀ z, A.thInd S N N' c x z =
    (((repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)).card : ℕ) : ℂ)⁻¹ *
      alV A.d A.sc (embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x)) *
      ∑ y ∈ S₁, alV A.d A.sc y * opU (HV A.sc) (-(embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x)))
        (opU (HV A.sc) y (sumU (HV A.sc) (alV A.d A.sc) S₂ (A.e a b N N'))) z

def RepsSplit : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B Λ : AddSubgroup V) (m₁ m₂ : ℕ), Nat.Coprime m₁ m₂ →
    (∀ y ∈ B, (((m₁ * m₂ : ℕ) : ℂ)) • y ∈ Λ) →
  ∀ SB S₁ S₂ : Finset V, IsReps Λ B SB → IsReps Λ (killIn (m₁ : ℂ) B Λ) S₁ → IsReps Λ (killIn (m₂ : ℂ) B Λ) S₂ →
    SB.card = S₁.card * S₂.card ∧ ∀ q : ℕ, q.Prime → q ∣ S₁.card → q ∣ m₁

def HalfKill : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ),
    IsSdLat N → IsSdLat N' → A.LaHyp a b S → 0 < c →
    ∀ y ∈ BC (X.embC A.σ₀) A.δ A.AA S N N' c, (c : ℂ) • y ∈ LamC (X.embC A.σ₀) A.δ A.AA N N'

def LiftKill : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c c' : ℕ) (x : HomE X.E a b),
    IsSdLat N → IsSdLat N' → A.LaHyp a b S → 0 < c → 0 < c' → c' ∣ c → x ∈ divLat c' (homAt S N N') →
    (c' : ℂ) • embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x) ∈ LamC (X.embC A.σ₀) A.δ A.AA N N'

def HalfP : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (p : ℕ), p.Prime → p ≠ 2 → ¬ p ∣ A.d →
    IsSdLat N → IsSdLat N' → A.LaHyp a b S →
  ∀ (π : ℂ) (pE : 𝓞 X.E), IsQInt A.d π → π * conj π = (p : ℂ) → SplitS A S p π pE →
  ∀ c' : ℕ, 0 < c' → ¬ p ∣ c' →
  ∀ S₂ : Finset (VCx X.Tau a b), IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (killIn (p : ℂ) (BC (X.embC A.σ₀) A.δ A.AA S N N' (p * c')) (LamC (X.embC A.σ₀) A.δ A.AA N N')) S₂ →
    IsReps (cLat (conj π) (LamC (X.embC A.σ₀) A.δ A.AA N N')) (cLat (conj π / π) (LamC (X.embC A.σ₀) A.δ A.AA N N')) S₂

def CardSAB : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ),
    IsSdLat N → IsSdLat N' → A.LaHyp a b S → 0 < c →
    (repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)).card = (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c)).card

def IdxPi : Prop :=
  ∀ (n : Type) [Fintype n] (Λ : AddSubgroup (n → ℂ)), IsLat Λ →
  ∀ (p : ℕ), p.Prime → ∀ π : ℂ, π * conj π = (p : ℂ) → (∀ x ∈ Λ, π • x ∈ Λ) → (∀ x ∈ Λ, conj π • x ∈ Λ) →
  ∀ Sa : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → Sa.card = p ^ Fintype.card n

def TaylorJet : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (a b : ℕ) (G : VCx T a b → ℂ), AnalyticOnNhd ℂ G Set.univ →
  ∀ m : DVar T a b →₀ ℕ,
    ((mfact m : ℕ) : ℂ) * MvPowerSeries.coeff m (taylorMv fun z => G (flat T a b z)) = derivAt0 G m

def LinSubDiag : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (d : n → K) (F : MvPowerSeries n K) (m : n →₀ ℕ),
    MvPowerSeries.coeff m (linSub (fun i k => if i = k then d k else 0) F) =
      (m.prod fun k e => d k ^ e) * MvPowerSeries.coeff m F

end Formalism.L2.AlgTh
