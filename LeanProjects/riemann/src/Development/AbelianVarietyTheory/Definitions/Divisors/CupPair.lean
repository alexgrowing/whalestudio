import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Abstract

variable {k : Type} [Field k] {M M' M₁ M₂ M₃ : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

structure Cx (k M : Type) [Field k] [AddCommGroup M] [Module k M] where

  C : ℤ → Submodule k M

  D : M →ₗ[k] M

namespace Cx

def IsCx (K : Cx k M) : Prop := ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

abbrev H (K : Cx k M) (n : ℤ) : Type := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

end Cx

def Adj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop :=
  ∀ n, ∃ ε : ℤˣ, ∀ a ∈ K.C n, ∀ b ∈ L.C (N - n - 1), β (K.D a) b = ε • β a (L.D b)

def Inj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N n : ℤ) : Prop :=
  ∀ a ∈ K.Z n, (∀ b ∈ L.Z (N - n), β a b = 0) → a ∈ K.B n

def Surj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N n : ℤ) : Prop :=
  ∀ φ : Module.Dual k M', (∀ b ∈ L.B (N - n), φ b = 0) → ∃ a ∈ K.Z n, ∀ b ∈ L.Z (N - n), φ b = β a b

def Perf (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop := ∀ n, Inj K L β N n ∧ Surj K L β N n

def IsMap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') : Prop := ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

structure SES (K₁ : Cx k M₁) (K₂ : Cx k M₂) (K₃ : Cx k M₃) (f : M₁ →ₗ[k] M₂) (g : M₂ →ₗ[k] M₃) : Prop where
  cx₁ : K₁.IsCx
  cx₂ : K₂.IsCx
  cx₃ : K₃.IsCx
  mapf : IsMap K₁ K₂ f
  mapg : IsMap K₂ K₃ g
  inj : ∀ n, ∀ a ∈ K₁.C n, f a = 0 → a = 0
  exact : ∀ n, ∀ a ∈ K₂.C n, g a = 0 ↔ ∃ a' ∈ K₁.C n, f a' = a
  surj : ∀ n, ∀ c ∈ K₃.C n, ∃ a ∈ K₂.C n, g a = c

structure DualSES {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂] [Module k N₂] [AddCommGroup N₃] [Module k N₃]
    (K₁ : Cx k M₁) (K₂ : Cx k M₂) (K₃ : Cx k M₃) (f : M₁ →ₗ[k] M₂) (g : M₂ →ₗ[k] M₃)
    (L₁ : Cx k N₁) (L₂ : Cx k N₂) (L₃ : Cx k N₃) (f' : N₂ →ₗ[k] N₁) (g' : N₃ →ₗ[k] N₂)
    (β₁ : M₁ →ₗ[k] N₁ →ₗ[k] k) (β₂ : M₂ →ₗ[k] N₂ →ₗ[k] k) (β₃ : M₃ →ₗ[k] N₃ →ₗ[k] k) (N : ℤ) : Prop where
  left : SES K₁ K₂ K₃ f g
  right : SES L₃ L₂ L₁ g' f'
  adj : Adj K₂ L₂ β₂ N
  adjf : ∀ n, ∀ a ∈ K₁.C n, ∀ b ∈ L₂.C (N - n), β₂ (f a) b = β₁ a (f' b)
  adjg : ∀ n, ∀ a ∈ K₂.C n, ∀ b ∈ L₃.C (N - n), β₂ a (g' b) = β₃ (g a) b

def pt (k : Type) [Field k] : Cx k k := ⟨fun n => if n = 0 then ⊤ else ⊥, 0⟩

end Abstract

section Cech

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

variable (k ι E) in

def deltaL : (Finset ι → E) →ₗ[k] (Finset ι → E) where
  toFun := GlobalTheory.DI.delta
  map_add' a b := by
    funext t
    simp [GlobalTheory.DI.delta, Finset.sum_add_distrib]
  map_smul' r a := by
    funext t
    simp only [GlobalTheory.DI.delta, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def cechC (F : Finset ι → Submodule k E) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥

def cech (F : Finset ι → Submodule k E) : Cx k (Finset ι → E) := ⟨cechC F, deltaL k ι E⟩

def totD (d : E →ₗ[k] E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  deltaL k ι E + LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • (d ∘ₗ LinearMap.proj s)

def totC (T : ℕ → Finset ι → Submodule k E) (a b : ℕ) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s =>
    if s.Nonempty ∧ (a : ℤ) ≤ n + 1 - s.card ∧ n + 1 - s.card < b then T (n + 1 - s.card).toNat s else ⊥

def cupPair [Fintype ι] {E' : Type} [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) :
    (Finset ι → E) →ₗ[k] (Finset ι → E') →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j))) (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end Cech

section Alg

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [Ring E] [Algebra k E]

structure IsDga (sg : E →ₐ[k] E) (d : E →ₗ[k] E) : Prop where
  sg_sg : ∀ x, sg (sg x) = x
  d_sg : ∀ x, d (sg x) = -sg (d x)
  d_mul : ∀ x y, d (x * y) = d x * y + sg x * d y
  d_d : ∀ x, d (d x) = 0

def cup (sg : E →ₐ[k] E) (a b : Finset ι → E) : Finset ι → E := fun u =>
  ∑ j ∈ u, (sg ^ ((u.filter (j ≤ ·)).card - 1)) (a (u.filter (· ≤ j))) * b (u.filter (j ≤ ·))

def tsg (sg : E →ₐ[k] E) (a : Finset ι → E) : Finset ι → E := fun s => (-1 : ℤ) ^ (s.card + 1) • sg (a s)

def const (x : E) : Finset ι → E := fun s => if s.card = 1 then x else 0

def cupPow (sg : E →ₐ[k] E) (a : Finset ι → E) (m : ℕ) : Finset ι → E :=
  Nat.rec (const 1) (fun _ y => cup sg y a) m

end Alg

end GlobalTheory.PD
