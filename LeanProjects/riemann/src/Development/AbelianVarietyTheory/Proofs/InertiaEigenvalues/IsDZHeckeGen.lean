import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfCompRangeRestrict
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinCuspOne

noncomputable section

open ValuativeRel Matrix GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.KTypeTest GlobalTheory.KTypeDatum GlobalTheory.DZero

namespace GlobalTheory.DZeroHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsDZType (π₀ : IrrGL k) {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀]
    (σ : Representation ℂ (GL (Fin π₀.1) 𝓀[k]) W₀) : Prop :=
  FiniteDimensional ℂ W₀ ∧ σ.IsIrreducible ∧ FinCusp σ ∧ ∃ j : W₀ →ₗ[ℂ] π₀.2.rep.V, HasType π₀.rep σ j

variable {d t N : ℕ}

abbrev dzBlocks (hN : ∑ _i : Fin t, d = N) : (Σ _a : Fin t, Fin d) ≃ Fin N :=
  stdBlocks (fun _ : Fin t => d) hN

variable (k) in

def dzJ (hN : ∑ _i : Fin t, d = N) : Subgroup (KO k (Fin N)) :=
  (parahoric k (dzBlocks hN)).subgroupOf (KO k (Fin N))

variable (k) in

def dzJIncl (hN : ∑ _i : Fin t, d = N) : dzJ k hN →* parahoric k (dzBlocks hN) :=
  (((KO k (Fin N)).subtype).comp (dzJ k hN).subtype).codRestrict _ fun x => x.2

def dzTau {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) : Representation ℂ (dzJ k hN) (PiTensorProduct ℂ fun _a : Fin t => W₀) :=
  (piTensor fun _a : Fin t => σ).comp ((parahoricProj k (dzBlocks hN)).comp (dzJIncl k hN))

def dzPerm (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Equiv.Perm (Fin N) :=
  if h : i + 1 < t then
    ((dzBlocks hN).symm.trans (Equiv.sigmaCongrLeft (β := fun _ : Fin t => Fin d) (Equiv.swap (⟨i, by omega⟩ : Fin t) ⟨i + 1, h⟩))).trans (dzBlocks hN)
  else 1

variable (k) in

def dzW (hN : ∑ _i : Fin t, d = N) (i : ℕ) : KO k (Fin N) :=
  toKO k (Fin N) ((Matrix.permMatrixHom (R := 𝒪[k])).toHomUnits (dzPerm hN i))

variable (k) in

def dzCoset (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Set (KO k (Fin N)) :=
  {g | ∃ a b : dzJ k hN, g = (a : KO k (Fin N)) * dzW k hN i * b}

def IsDZHeckeGen {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) (q : ℕ) (i : ℕ) (T : Module.End ℂ (indSpace (dzJ k hN) (dzTau σ hN))) : Prop :=
  (∀ κ : KO k (Fin N), T * ind (dzJ k hN) (dzTau σ hN) κ = ind (dzJ k hN) (dzTau σ hN) κ * T) ∧
    (T - (q : ℂ) • 1) * (T + 1) = 0 ∧
    ∀ f : indSpace (dzJ k hN) (dzTau σ hN), (∀ g ∈ dzCoset k hN i, f.1 g = 0) → (T f).1 1 = 0

variable (k) in

def dzQ (d : ℕ) : ℕ := resCard k ^ d

def dzT {W₀ : Type} [AddCommGroup W₀] [Module ℂ W₀] (σ : Representation ℂ (GL (Fin d) 𝓀[k]) W₀)
    (hN : ∑ _i : Fin t, d = N) (i : ℕ) : Module.End ℂ (indSpace (dzJ k hN) (dzTau σ hN)) :=
  Classical.epsilon (IsDZHeckeGen σ hN (dzQ k d) i)

end GlobalTheory.DZeroHecke
