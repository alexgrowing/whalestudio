import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.WpFam

def Tr {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1

structure IsTr {K : Type} [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) : Prop where

  sub : ∀ x x' y y', T x x' → T y y' → T (x - y) (x' - y')

  mem_iff : ∀ x x', T x x' → (ι x ∈ Λ₀.lattice ↔ ι x' ∈ Λ₁.lattice)

  triv : ∀ x x', ι x ∈ Λ₀.lattice → ι x' ∈ Λ₁.lattice → T x x'

  left : ∀ x, ∃ x', T x x'

  right : ∀ x', ∃ x, T x x'

  rat₀ : ∀ z ∈ Λ₀.lattice, ∃ k, ι k = z

  rat₁ : ∀ z ∈ Λ₁.lattice, ∃ k, ι k = z

end GlobalTheory.WpFam
