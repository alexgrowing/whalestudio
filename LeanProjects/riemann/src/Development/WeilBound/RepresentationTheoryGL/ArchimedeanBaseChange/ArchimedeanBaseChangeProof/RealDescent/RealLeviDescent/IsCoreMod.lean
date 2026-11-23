import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Formalism.RealPlaceAnalysis.StatementA

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgTw (Mat G th)
open PositivityTheory.RgBcC.Real
open Formalism.REAL (GlRel)

variable {n : ℕ}

open Classical in

def trOn {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (f : M →ₗ[ℂ] M) : ℂ :=
  if h : ∀ x ∈ S, f x ∈ S then LinearMap.trace ℂ S (f.restrict h) else 0

def dualT (E : KMod n) (T : E.V →L[ℂ] E.V) : (E.V →L[ℂ] ℂ) →L[ℂ] (E.V →L[ℂ] ℂ) :=
  (ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip T

section U

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : G n →* (U →L[ℂ] U))

def invSp (E : KMod n) : Submodule ℂ ((E.V →L[ℂ] ℂ) →L[ℂ] U) where
  carrier := {t | IsInvT π E t}
  add_mem' {a b} ha hb k ξ := by
    simp only [ContinuousLinearMap.add_apply, map_add]
    rw [ha k ξ, hb k ξ]
  zero_mem' k ξ := by simp
  smul_mem' c a ha k ξ := by
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [ha k ξ]

def flipU (E : KMod n) (A : U →L[ℂ] U) (T : E.V →L[ℂ] E.V) :
    ((E.V →L[ℂ] ℂ) →L[ℂ] U) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →L[ℂ] U) where
  toFun t := A.comp (t.comp (dualT E T))
  map_add' x y := by simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c x := by simp [ContinuousLinearMap.smul_comp]

def trInv (E : KMod n) (A : U →L[ℂ] U) (T : E.V →L[ℂ] E.V) : ℂ := trOn (invSp π E) (flipU E A T)

end U

section Alg

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def epow (E : Fin n → Fin n → Module.End ℂ V) : ℕ → Fin n → Fin n → Module.End ℂ V
  | 0, a, b => if a = b then 1 else 0
  | m + 1, a, b => ∑ c, E a c * epow E m c b

def gelA (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) : Module.End ℂ V := ∑ a, epow E m a a

def kF (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ V := fun a b => E1 a b + E2 a b

def pF (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ V := fun a b => E1 a b - E2 a b

def barF (E2 : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ V := fun a b => -E2 b a

def alg (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Subalgebra ℂ (Module.End ℂ V) :=
  Algebra.adjoin ℂ {x | ∃ a b, x = E1 a b ∨ x = E2 a b}

structure IsPair (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b
  unitK : ∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ
  unitP : ∀ a b (x y : V), ⟪pF E1 E2 a b x, y⟫_ℂ = -⟪x, pF E1 E2 b a y⟫_ℂ

def IsDerivK (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V) : Prop :=
  (∀ k (x y : V), ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
  ∀ v : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ v ∈ S ∧ (∀ k, ∀ w ∈ S, σ k w ∈ S) ∧
    (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) ∧
    ∀ (X : Mat n) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ w ∈ S, HasDerivAt (fun t : ℝ => σ (γ t) w) (∑ a, ∑ b, X a b • Kf a b w) 0

structure IsCoreMod (χ : Inf n) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V) : Prop where
  pair : IsPair E1 E2
  ch1 : ∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (χ true) m • x
  ch2 : ∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (χ false) m • x
  nontriv : Nontrivial V
  irr : ∀ v w : V, v ≠ 0 → ∃ x ∈ alg E1 E2, x v = w
  der : IsDerivK σ (kF E1 E2)
  Asq : A * A = 1
  Aiso : ∀ x y : V, ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ
  Aσ : ∀ k, A * σ k = σ k * A
  AE : ∀ a b, A * E1 a b = E2 a b * A

def invA (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (E : KMod n) : Submodule ℂ ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V) where
  carrier := {t | ∀ k ξ, t (ξ ∘L E.ρ k⁻¹) = σ k (t ξ)}
  add_mem' {a b} ha hb k ξ := by
    simp only [LinearMap.add_apply, map_add]
    rw [ha k ξ, hb k ξ]
  zero_mem' k ξ := by simp
  smul_mem' c a ha k ξ := by
    simp only [LinearMap.smul_apply, map_smul]
    rw [ha k ξ]

def flipA (E : KMod n) (A : V →ₗ[ℂ] V) (T : E.V →L[ℂ] E.V) :
    ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V) where
  toFun t := A.comp (t.comp (dualT E T).toLinearMap)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def hwSp (E1 E2 : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) : Submodule ℂ V where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm], fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

end Alg

def rhoV (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - (a : ℕ)

def IsLev (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Prop := Monotone lev ∧ ∀ a b, lev a = lev b → lam a = lam b

def rhoU (lev : Fin n → ℕ) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => lev a < lev b).card : ℝ) - ((univ.filter fun b => lev b < lev a).card : ℝ)) / 2

def muQ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℝ := fun a => 2 * (lam a : ℝ) + 2 * rhoU lev a

open Classical in

def harmSet (lam : Fin n → ℤ) : Finset (Fin n → ℝ) :=
  ((univ : Finset (Fin n → Fin n)).filter fun lev => IsLev lam fun a => (lev a : ℕ)).image fun lev => muQ lam fun a => (lev a : ℕ)

def m0 (lam : Fin n → ℤ) : Fin n → ℝ := fun a => 2 * (lam a : ℝ) + ((n : ℝ) - 1) - 2 * (a : ℕ)

theorem trOn_bot {M : Type*} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] M) : trOn ⊥ f = 0 := by
  unfold trOn
  split_ifs with h
  · rw [show f.restrict h = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  · rfl

end PositivityTheory.RgBcC.RealD
