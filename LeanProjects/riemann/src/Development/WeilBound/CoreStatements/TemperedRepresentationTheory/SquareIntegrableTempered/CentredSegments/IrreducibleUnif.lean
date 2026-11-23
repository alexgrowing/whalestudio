import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp

noncomputable section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

namespace Zls

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def unif : 𝒪[k] := Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[k])

theorem irreducible_unif : Irreducible (unif k) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible 𝒪[k])

variable (k) in

def unifU : kˣ :=
  Units.mk0 (algebraMap 𝒪[k] k (unif k))
    ((map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2 irreducible_unif.ne_zero)

variable (k) in

def Km (N m : ℕ) : Subgroup (GL (Fin N) k) :=
  ((Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {unif k ^ m}))).ker).map
    (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k))

variable (k) in

def diagPow (N : ℕ) (lam : Fin N → ℤ) : GL (Fin N) k :=
  Units.map (Matrix.diagonalRingHom (Fin N) k).toMonoidHom (MulEquiv.piUnits.symm fun i => unifU k ^ lam i)

def lamOf {N : ℕ} (g : Fin (N - 1) → ℕ) : Fin N → ℤ :=
  fun i => ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) then (g j : ℤ) else 0

def omegaVec (N j : ℕ) : Fin N → ℤ := fun i => if (i : ℕ) < j then 1 else 0

def IsHeckeOp {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ)
    (g : GL (Fin N) k) (T : Module.End ℂ (fixed π (Km k N m))) : Prop :=
  ∀ (v : fixed π (Km k N m)) (l : Module.Dual ℂ V), (∀ x ∈ Km k N m, l ∘ₗ π x = l) →
    l (π g (v : V)) = l ((T v : fixed π (Km k N m)) : V)

def HeckeSpectral {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ, 0 < j → j < N → ∀ T : Module.End ℂ (fixed π (Km k N m)),
    IsHeckeOp π m (diagPow k N (omegaVec N j)) T → ∀ μ : ℂ, T.HasEigenvalue μ →
      ‖μ‖ < (Nat.card 𝓀[k] : ℝ) ^ (-(((j * (N - j) : ℕ) : ℝ) / 2))

def UnitaryCentral {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ (t : kˣ) (c : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → ‖c‖ = 1

def MaxExpStrict {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → Zc.jm x hd π ≠ 0 → Zl.ExpStrict x

variable (k) in

def CasselmanSuffSq : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    1 ≤ N → IsSmooth π → π.IsIrreducible → UnitaryCentral π → MaxExpStrict π → IsSqIntCoeff π

end Zls

end
