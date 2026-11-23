import Mathlib
open Finset

noncomputable section

namespace PI.RamBound

def geV (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (x : Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Kc) ^ (-a) ∈ Oc

def gaussGe (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) {τ : Type} (y : MvPolynomial τ Kc) (g : ℝ) : Prop :=
  ∀ n, geV p Oc (MvPolynomial.coeff n y) g

def JetInt {Kc : Type} [Field Kc] (Oc : Subring Kc) {σ : Type} (f : MvPowerSeries σ Kc) : Prop :=
  ∀ n : σ →₀ ℕ, (∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f ∈ Oc

def IsPart {n' : ℕ} (r0 : ℕ) (nu : Fin n' → ℕ → ℤ) : Prop :=
  (∀ s i, 0 ≤ nu s i) ∧ (∀ s i, 1 ≤ i → nu s (i + 1) ≤ nu s i) ∧ (∀ s i, r0 < i → nu s i = 0)

def sz {n' : ℕ} (rb : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := ∑ i ∈ Icc 1 rb, nu s i

abbrev ZV (nH r0 r1 : ℕ) : Type := Σ _t : Fin nH, Fin 2 × Fin r0 × Fin r1

abbrev FrV (nH r0 : ℕ) : Type := Σ _t : Fin nH, Fin 2 × ℕ × Fin r0

abbrev Wt (nH : ℕ) : Type := Fin nH → Fin 2 → ℕ → ℤ

abbrev ColCh (nH r1 : ℕ) : Type := Fin nH → Fin 2 → ℕ → ℕ → Fin r1

def colHt {nH : ℕ} (rb : ℕ) (nu : Wt nH) (v : Fin nH) (s : Fin 2) (c : ℕ) : ℕ :=
  ((Icc 1 rb).filter fun i => (c : ℤ) < nu v s i).card

def colFac {nH r0 r1 : ℕ} (rb : ℕ) (nu : Wt nH) (I : ColCh nH r1) (v : Fin nH) (s : Fin 2) (c : ℕ) :
    MvPolynomial (ZV nH r0 r1) (MvPolynomial (FrV nH r0) ℤ) :=
  Matrix.det (Matrix.of fun (i i' : Fin (colHt rb nu v s c)) =>
    ∑ a : Fin r0,
      MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : FrV nH r0)) *
        MvPolynomial.X (⟨v, (s, a, I v s c i'.val)⟩ : ZV nH r0 r1))

def prodP {nH r0 r1 : ℕ} (rb : ℕ) (nu : Wt nH) (I : ColCh nH r1) : MvPolynomial (ZV nH r0 r1) (MvPolynomial (FrV nH r0) ℤ) :=
  ∏ v : Fin nH, ∏ s : Fin 2, ∏ c ∈ range (nu v s 1).toNat, colFac rb nu I v s c

def applyD {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    MvPolynomial τ Kc :=
  ∑ n ∈ P.support, ((∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f) •
    MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n P)

def KG {Kc : Type} [Field Kc] (Oc : Subring Kc) (nH r0 r1 rb : ℕ) (nu : Wt nH) (Th : MvPowerSeries (ZV nH r0 r1) Kc) :
    AddSubgroup (MvPolynomial (FrV nH r0) Kc) :=
  AddSubgroup.closure {y | ∃ (I : ColCh nH r1) (g : MvPolynomial (FrV nH r0) Kc), (∀ n, MvPolynomial.coeff n g ∈ Oc) ∧
    y = g * applyD (prodP (r0 := r0) rb nu I) Th}

def beD {Kc : Type} [Field Kc] (nH r0 r1 : ℕ) (u : Fin nH → Kc) : MvPowerSeries (ZV nH r0 r1) Kc :=
  ∑ t : Fin nH, MvPowerSeries.C (u t) * ∑ a : Fin r0, ∑ b : Fin r1,
    MvPowerSeries.X (⟨t, ((0 : Fin 2), a, b)⟩ : ZV nH r0 r1) *
      MvPowerSeries.X (⟨t, ((1 : Fin 2), a, b)⟩ : ZV nH r0 r1)

def expK {Kc : Type} [Field Kc] {σ : Type} (f : MvPowerSeries σ Kc) : MvPowerSeries σ Kc :=
  fun n => ∑ k ∈ range (n.degree + 1), ((k.factorial : Kc))⁻¹ * MvPowerSeries.coeff n (f ^ k)

def IntD (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (nH r0 r1 : ℕ) (Th : MvPowerSeries (ZV nH r0 r1) Kc) : Prop :=
  ∃ (S : Kc) (u : Fin nH → Kc) (F0 : MvPowerSeries (ZV nH r0 r1) Kc),
    geV p Oc S (-(1 / 2)) ∧ (∀ t, u t ∈ Oc) ∧ JetInt Oc F0 ∧
      Th = expK (-(MvPowerSeries.C S) * beD nH r0 r1 u) * F0

def ct {nH : ℕ} (rb : ℕ) (TT : Finset (Fin nH)) (nu : Fin nH → Fin 2 → ℕ → ℤ) (t : Fin nH) : ℤ :=
  sz rb (nu t) 0 - (if t ∈ TT then nu t 0 1 - nu t 0 2 else 0) + (if t ∈ TT then nu t 1 1 else 0)

end PI.RamBound

open PI.RamBound in

def PI.RamBound : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (nH r0 r1 rb : ℕ) (TT : Finset (Fin nH)) (nu : Wt nH)
    (Th : MvPowerSeries (ZV nH r0 r1) Kc),
    p.Prime → (∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc) → ((p : Kc))⁻¹ ∉ Oc → (∀ t, IsPart r0 (nu t)) → r0 ≤ rb →
      IntD p Oc nH r0 r1 Th →
      ∀ y ∈ KG Oc nH r0 r1 rb nu Th, gaussGe p Oc y (-(1 / 2) * ∑ t, (ct rb TT nu t : ℝ))
