import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableOfCharOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportCharFn

noncomputable section

open GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest

namespace GlobalTheory.KTypeDatum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def InComp (π₀ y : IrrGL k) : Prop :=
  ∃ s : Multiset (IrrGL k), HasSupport y.rep s ∧ ∀ x ∈ s, IrrGL.Inert π₀ x

def IsSegFamily {r : ℕ} (y : Fin r → IrrGL k) : Prop :=
  (∀ j, (y j).IsEssSqInt) ∨ (∀ j, ∃ Δ : Segment k, IsLSeg Δ (y j).rep)

def IsJMap {N : ℕ} (J : Subgroup (KO k (Fin N))) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ J U) (ρ : Representation ℂ (GL (Fin N) k) V) (f : U →ₗ[ℂ] V) : Prop :=
  ∀ j : J, f ∘ₗ τ j = ρ ((j : KO k (Fin N)) : GL (Fin N) k) ∘ₗ f

def IsKTypeDatum (π₀ : IrrGL k) (t : ℕ) {N : ℕ} (J : Subgroup (KO k (Fin N))) {U : Type} [AddCommGroup U]
    [Module ℂ U] (τ : Representation ℂ J U) (S : Submodule ℂ (indSpace J τ))
    (hS : ∀ (κ : KO k (Fin N)), ∀ f ∈ S, ind J τ κ f ∈ S) : Prop :=
  (∃ K' : Subgroup (GL (Fin N) k), IsOpen (K' : Set (GL (Fin N) k)) ∧ K' ≤ KO k (Fin N) ∧
      (K'.subgroupOf (KO k (Fin N))).Normal ∧ (∀ κ : KO k (Fin N), (κ : GL (Fin N) k) ∈ K' → κ ∈ J) ∧
      ∀ j : J, ((j : KO k (Fin N)) : GL (Fin N) k) ∈ K' → τ j = 1) ∧
    FiniteDimensional ℂ S ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∃ j, ¬ InComp π₀ (y j)) →
      ∀ f, IsJMap J τ (prodIrr y hd) f → f = 0) ∧
    (∀ (r : ℕ) (y : Fin r → IrrGL k) (hd : ∑ j, (y j).1 = N), IsSegFamily y → (∀ j, InComp π₀ (y j)) →
      (∃ j, ¬ IrrGL.Inert π₀ (y j)) → ∀ f, IsKMap (KO k (Fin N)) (sub (ind J τ) S hS) (prodIrr y hd) f → f = 0) ∧
    ∃ (hN : ∑ _i : Fin t, π₀.1 = N) (f : S →ₗ[ℂ] _), f ≠ 0 ∧
      IsKMap (KO k (Fin N)) (sub (ind J τ) S hS) (prodIrr (fun _ : Fin t => π₀) hN) f

end GlobalTheory.KTypeDatum
