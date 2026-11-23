import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgTie
import Formalism.PadicSubsetSums.StableGradedCounts.IRRFrobOrbitIrred
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.CharacterEqOfRepIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.BlockSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.ExistsNeZeroTensor

open Polynomial CategoryTheory NumberField

noncomputable section

namespace Formalism.L2.Col

def XgBrauerSplit : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (K : Type) [Field K] (σ : K →+* ℂ) (z : K),
    IsPrimitiveRoot z (Fintype.card Γ) →
    ∀ (n : ℕ) (ρ : Representation ℂ Γ (Fin n → ℂ)), ρ.IsIrreducible →
      ∃ (m : ℕ) (τ : Representation K Γ (Fin m → K))
        (τb : Representation (AlgebraicClosure K) Γ (Fin m → AlgebraicClosure K)),
        τb.IsIrreducible ∧
        (∀ t, LinearMap.toMatrix' (τb t) = (LinearMap.toMatrix' (τ t)).map (algebraMap K (AlgebraicClosure K))) ∧
        ∀ t, σ (τ.character t) = ρ.character t

def XgGreenExists : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y) → Formalism.L2.NT.IsGenSys ζ →
    ∀ d k : ℕ, 0 < d → (Formalism.L2.NT.labCusp ζ d k).natDegree = d →
      ∃ χ : GL (Fin d) (ZMod g) → ℂ, Formalism.L2.NT.IsCuspChar χ ∧ Formalism.L2.NT.GreenAt teich χ k

section Rep

variable {Γ : Type} [Group Γ] [Fintype Γ]

end Rep

section Series

variable {g : ℕ} [Fact g.Prime]

end Series

section Assemble

theorem residueField_equiv_zmod {X : Fields} (w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.E)) (g : ℕ) [Fact g.Prime]
    (hw : Ideal.absNorm w.asIdeal = g) : Nonempty ((𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod g) := by
  have hc : Nat.card (𝓞 X.E ⧸ w.asIdeal) = g := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 X.E ⧸ w.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : g.Prime).ne_zero)
  letI : Fintype (𝓞 X.E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hc' : Fintype.card (𝓞 X.E ⧸ w.asIdeal) = g := by rw [← Nat.card_eq_fintype_card, hc]
  have : CharP (𝓞 X.E ⧸ w.asIdeal) g := charP_of_card_eq_prime hc'
  exact ⟨(ZMod.ringEquiv _ hc').symm⟩

def generalLinearEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (r : ℕ) (e : R ≃+* S) : GL (Fin r) R ≃* GL (Fin r) S :=
  Units.mapEquiv (e.mapMatrix (m := Fin r)).toMulEquiv

def XgNonemp : Prop :=
  XgBrauerSplit → XgGreenExists →
  ∀ {X : Fields} (Pr : Primes X) {m : ℕ} (Ch : Chars X Pr m) (r : ℕ)
    [∀ i, Fact (Pr.g i).Prime] (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ)
    (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i)),
    XgNonempty Pr Ch r σ teich ζ

end Assemble

end Formalism.L2.Col
