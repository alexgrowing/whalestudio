import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

noncomputable section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace UpperTheory.Lit.Cas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def jm {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : ℕ∞ :=
  jhMult (piTensor fun a => (x a).rep) (jac (stdBlocks (fun a => (x a).1) hd) π)

def ScalarBy (x : IrrGL k) (t : kˣ) (c : ℂ) : Prop :=
  ∀ v, x.rep (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) v = c • v

def ExpStrict {h : ℕ} (x : Fin h → IrrGL k) : Prop :=
  ∀ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → ∀ c : Fin h → ℂ, (∀ i, ScalarBy (x i) t (c i)) →
    (∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), ‖c i‖ < 1) ∧ ∏ i, ‖c i‖ = 1

def ExpWeak {h : ℕ} (x : Fin h → IrrGL k) : Prop :=
  ∀ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → ∀ c : Fin h → ℂ, (∀ i, ScalarBy (x i) t (c i)) →
    (∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), ‖c i‖ ≤ 1) ∧ ∏ i, ‖c i‖ = 1

variable (k) in

def CasselmanNecSq : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π →
      ∀ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → jm x hd π ≠ 0 → ExpStrict x

def UnitaryCentral {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ (t : kˣ) (c : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → ‖c‖ = 1

def MaxExpWeak {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → jm x hd π ≠ 0 → ExpWeak x

variable (k) in

def CasselmanSuffTemp : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    1 ≤ N → IsSmooth π → π.IsIrreducible → UnitaryCentral π → MaxExpWeak π → IsTemperedCoeff π

end UpperTheory.Lit.Cas

end
