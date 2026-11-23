import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

open Polynomial Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable (D : D7)

abbrev plBar (k : Fin 2) (v : D.nd.PlG k) : ValuationSubring D.nd.Om :=
  D.nd.plOm.1 (D.naut.plGw k v)

def Guard (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) : Prop :=
  D.nd.goodRow σ ∧ D.ntypes.cuspidal σ ∧ D.what₂.isot (D.nd.j i) σ ≠ ⊥ ∧ D.nd.l i ≠ D.host.g k

def IsFrobAtType (k : Fin 2) (v : D.nd.PlG k) (φ : G D.host.E D.nd.Om) : Prop :=
  IsFrob (F := D.host.E) (plBar D k v) (normV (D.naut.plGw k v)) φ

def IsWildAtType (k : Fin 2) (v : D.nd.PlG k) (s : G D.host.E D.nd.Om) : Prop :=
  ∀ y : D.nd.Om, y ≠ 0 → (plBar D k v).valuation (s y / y - 1) < 1

def TameEigenvalues (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
      Matrix (Fin D.R.r) (Fin D.R.r)
        (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
    ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
      X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod

def FrobConj (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k)
    (φ : G D.host.E D.nd.Om) : Prop :=
  D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) =
    D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

def TameGeneratorAtTypePrime : Prop :=
  ∀ (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2), Guard D σ i k → ∀ v : D.nd.PlG k,
    TameEigenvalues D σ i k v ∧ ∃ φ : G D.host.E D.nd.Om, IsFrobAtType D k v φ ∧ FrobConj D σ i k v φ

def TameAtTypePrimeStrong : Prop :=
  ∀ (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2), Guard D σ i k → ∀ v : D.nd.PlG k,
    (∀ s : G D.host.E D.nd.Om, IsWildAtType D k v s → D.ntypes.rbar σ (D.nd.w i) s = 1) ∧
    TameEigenvalues D σ i k v ∧
    ∀ φ : G D.host.E D.nd.Om, IsFrobAtType D k v φ → FrobConj D σ i k v φ

theorem exists_isFrobAtType (k : Fin 2) (v : D.nd.PlG k) : ∃ φ, IsFrobAtType D k v φ :=
  exists_isFrob (D.nd.plOm.2 _)

theorem tameGenerator_of_strong (h : TameAtTypePrimeStrong D) : TameGeneratorAtTypePrime D := by
  intro σ i k hg v
  obtain ⟨φ, hφ⟩ := exists_isFrobAtType D k v
  exact ⟨(h σ i k hg v).2.1, φ, hφ, (h σ i k hg v).2.2 φ hφ⟩

theorem root_ne_zero (σ : D.what₂.FT) (hσ : D.nd.goodRow σ) (k : Fin 2) (v : D.nd.PlG k) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v), x ≠ 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rintro x hx rfl
  have h0 := ((hσ k).1.1 v).2.2
  have hr := (Polynomial.mem_roots'.mp hx).2
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hr
  exact h0 ((map_eq_zero_iff _ (algebraMap (ZMod (D.host.g k)) _).injective).mp hr)

example (i : D.nd.Loc) : D.what₂.places.resChar (D.nd.w i) = D.nd.l i := D.nd.w_l i

end GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

end
