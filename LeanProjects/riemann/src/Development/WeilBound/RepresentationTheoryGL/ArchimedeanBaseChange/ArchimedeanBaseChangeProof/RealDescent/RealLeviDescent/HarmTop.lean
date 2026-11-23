import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def hwK {W : Type*} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) : Submodule ℂ W where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) F μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm], fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def IsDerE (E : KMod n) (F : Fin n → Fin n → Module.End ℂ E.V) : Prop :=
  ∀ (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
    ∀ w : E.V, HasDerivAt (fun t : ℝ => E.ρ (γ t) w) (∑ a, ∑ b, X a b • F a b w) 0

def dualF (E : KMod n) (F : Fin n → Fin n → Module.End ℂ E.V) : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ) :=
  fun a b => -((ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip (LinearMap.toContinuousLinearMap (F a b))).toLinearMap

def castW (ν : Fin n → ℤ) : Fin n → ℝ := fun a => (ν a : ℝ)

def chE (lam : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2

def tchE (lam : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam fun a => z a ^ 2

def IsExp (f : (Fin n → ℂ) → ℂ) (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℤ) : Prop :=
  (∀ ν ∈ S, Antitone ν) ∧ ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → (Function.Injective fun a => z a ^ 2) →
    f z = ∑ ν ∈ S, (c ν : ℂ) * weylChar ν z

def DerEx : Prop := ∀ (n : ℕ) (E : KMod n), ∃ F, IsDerE E F

def HomDec : Prop :=
  ∀ (n : ℕ) (χ : Inf n) (E : KMod n) (T : E.V →L[ℂ] E.V) (F : Fin n → Fin n → Module.End ℂ E.V), IsDerE E F →
    (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod χ E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) →
      ∃ S : Finset (Fin n → ℝ), (∀ ν, hwK (dualF E F) ν ≠ ⊥ ↔ ν ∈ S) ∧
        (∀ ν ∈ S, FiniteDimensional ℂ (hwSp E1 E2 ν)) ∧ (invA σ E ≠ ⊥ → ∃ ν ∈ S, hwSp E1 E2 ν ≠ ⊥) ∧
        trOn (invA σ E) (flipA E A T) =
          ∑ ν ∈ S, trOn (hwK (dualF E F) ν) (dualT E T).toLinearMap * trOn (hwSp E1 E2 ν) A

def WtE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V) (F : Fin n → Fin n → Module.End ℂ E.V), IsLefK lam E T →
    IsDerE E F → ∀ (S : Finset (Fin n → ℤ)) (d c : (Fin n → ℤ) → ℤ), IsExp (chE lam) S d → IsExp (tchE lam) S c →
      (∀ μ : Fin n → ℝ, hwK (dualF E F) μ ≠ ⊥ → ∃ ν ∈ S, castW ν = μ ∧ d ν ≠ 0) ∧
      ∀ ν ∈ S, Module.finrank ℂ (hwK (dualF E F) (castW ν)) = d ν ∧
        trOn (hwK (dualF E F) (castW ν)) (dualT E T).toLinearMap = c ν

def ExpEx : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∃ (S : Finset (Fin n → ℤ)) (d c : (Fin n → ℤ) → ℤ),
    IsExp (chE lam) S d ∧ IsExp (tchE lam) S c

def CoefE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (S : Finset (Fin n → ℤ)) (d c : (Fin n → ℤ) → ℤ),
    IsExp (chE lam) S d → IsExp (tchE lam) S c →
      (∀ ν ∈ S, d ν ≠ 0 → inCone (fun a => (a : ℕ)) (m0 lam - castW ν)) ∧
      ∀ μ ∈ harmSet lam, ∃ ν ∈ S, castW ν = μ ∧ d ν ≠ 0 ∧ c ν = 2 ^ n

def DomSel : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ ν : Fin n → ℤ, Antitone ν →
    inCone (fun a => (a : ℕ)) (m0 lam - castW ν) → LSq lam ≤ spinSq (castW ν) → castW ν ∈ harmSet lam

def HarmTop : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam

end PositivityTheory.RgBcC.RealD
