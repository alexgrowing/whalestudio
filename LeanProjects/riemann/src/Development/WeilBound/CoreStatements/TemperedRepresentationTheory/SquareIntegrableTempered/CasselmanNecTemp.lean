import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

noncomputable section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace Zl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

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
      ∀ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → ExpStrict x

variable (k) in

def CasselmanNecTemp : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π →
      ∀ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → ExpWeak x

end Zl

end
