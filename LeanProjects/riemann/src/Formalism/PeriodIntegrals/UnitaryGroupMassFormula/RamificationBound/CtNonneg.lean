import Mathlib
import Formalism.PeriodIntegrals.RamBound

open Finset MvPolynomial PI.RamBound

noncomputable section

namespace PI.RamBoundW

abbrev Fr (nH r0 : ℕ) : Type := MvPolynomial (FrV nH r0) ℤ

def lap {R : Type} [CommRing R] {nH r0 r1 : ℕ} (t : Fin nH) :
    Module.End R (MvPolynomial (ZV nH r0 r1) R) :=
  ∑ a : Fin r0, ∑ b : Fin r1,
    (pderiv (⟨t, ((0 : Fin 2), a, b)⟩ : ZV nH r0 r1)).toLinearMap ∘ₗ
      (pderiv (⟨t, ((1 : Fin 2), a, b)⟩ : ZV nH r0 r1)).toLinearMap

def Vanish : Prop :=
  ∀ (nH r0 r1 rb : ℕ) (TT : Finset (Fin nH)) (nu : Wt nH) (I : ColCh nH r1),
    (∀ t, IsPart r0 (nu t)) → r0 ≤ rb → ∀ (t : Fin nH) (k : ℕ), ct rb TT nu t < k →
      ((lap (R := Fr nH r0) t) ^ k) (prodP (r0 := r0) rb nu I) = 0

def Contract : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (nH r0 r1 : ℕ) (c : Fin nH → ℕ)
    (P : MvPolynomial (ZV nH r0 r1) (Fr nH r0)) (Th : MvPowerSeries (ZV nH r0 r1) Kc),
    p.Prime → (∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) → ((p : Kc))⁻¹ ∉ Oc → IntD p Oc nH r0 r1 Th →
    (∀ t k, c t < k → ((lap (R := Fr nH r0) t) ^ k) P = 0) →
      gaussGe p Oc (applyD P Th) (-(1 / 2) * ∑ t, (c t : ℝ))

def GaussAlg : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (τ : Type) (g : ℝ),
    p.Prime → (∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) → ((p : Kc))⁻¹ ∉ Oc →
    gaussGe p Oc (0 : MvPolynomial τ Kc) g ∧
    (∀ y y' : MvPolynomial τ Kc, gaussGe p Oc y g → gaussGe p Oc y' g → gaussGe p Oc (y + y') g) ∧
    (∀ y : MvPolynomial τ Kc, gaussGe p Oc y g → gaussGe p Oc (-y) g) ∧
    (∀ w y : MvPolynomial τ Kc, (∀ n, coeff n w ∈ Oc) → gaussGe p Oc y g → gaussGe p Oc (w * y) g)

def CtNonneg : Prop :=
  ∀ (nH r0 rb : ℕ) (TT : Finset (Fin nH)) (nu : Wt nH),
    (∀ t, IsPart r0 (nu t)) → r0 ≤ rb → ∀ t, 0 ≤ ct rb TT nu t

end PI.RamBoundW
