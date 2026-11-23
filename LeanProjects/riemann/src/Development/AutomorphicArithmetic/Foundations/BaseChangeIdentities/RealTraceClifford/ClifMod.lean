import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.RealTr

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel IsWeight KHighest)

variable {n : ℕ}

abbrev Wt (n : ℕ) : Type := Fin n → ℝ

abbrev FR (n : ℕ) : Type := AddMonoidAlgebra ℂ (Wt n)

def ex (x : Wt n) : FR n := AddMonoidAlgebra.single x 1

def cf (f : FR n) (x : Wt n) : ℂ := f.coeff x

def sg (w : Equiv.Perm (Fin n)) : ℂ := ((Equiv.Perm.sign w : ℤ) : ℂ)

def alt (x : Wt n) : FR n := ∑ w : Equiv.Perm (Fin n), sg w • ex (x ∘ w)

def rt (a b : Fin n) : Wt n := Pi.single a 1 - Pi.single b 1

def posP (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

def chR (n : ℕ) : FR n := ex (rhoV n) * ∏ p ∈ posP n, (1 + ex (-rt p.1 p.2))

def Sym (f : FR n) : Prop := ∀ (w : Equiv.Perm (Fin n)) x, cf f (x ∘ w) = cf f x

def ASym (f : FR n) : Prop := ∀ (w : Equiv.Perm (Fin n)) x, cf f (x ∘ w) = sg w * cf f x

def Dom (x : Wt n) : Prop := ∀ a b, a < b → ∃ m : ℕ, x a - x b = m

def Maj (ξ κ : Wt n) : Prop := ∀ x : Wt n, Antitone x → ∑ a, x a * ξ a ≤ ∑ a, x a * κ a

def evT (θ : Wt n) : FR n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Wt n)
    { toFun := fun x => Complex.exp (Complex.I * ∑ a, (θ a : ℂ) * (x.toAdd a : ℂ))
      map_one' := by simp
      map_mul' := fun x y => by simp [← Complex.exp_add, mul_add, Finset.sum_add_distrib] }

def twoL (lam : Fin n → ℤ) : Wt n := fun a => 2 * (lam a : ℝ) + 2 * rhoV n a

section Mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def wsp (F : Fin n → Fin n → Module.End ℂ V) (μ : Wt n) : Submodule ℂ V where
  carrier := {v | IsWeight F μ v}
  add_mem' {x y} hx hy := fun a => by rw [map_add, hx a, hy a, smul_add]
  zero_mem' := fun a => by simp
  smul_mem' c x hx := fun a => by rw [map_smul, hx a, smul_comm]

def hw (F : Fin n → Fin n → Module.End ℂ V) (μ : Wt n) : Submodule ℂ V where
  carrier := {v | KHighest (fun _ => true) F μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm],
    fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def Stb (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) : Prop := ∀ a b, ∀ x ∈ S, F a b x ∈ S

def Cm (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (B : Module.End ℂ V) : Prop :=
  (∀ a b, B * F a b = F a b * B) ∧ ∀ x ∈ S, B x ∈ S

def IsCh (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (B : Module.End ℂ V) (c : FR n) : Prop :=
  ∀ μ, cf c μ = trOn (wsp F μ ⊓ S) B

def LocF (F : Fin n → Fin n → Module.End ℂ V) : Prop := ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ Stb F S

def homL {N : Type} [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N) (K : Fin n → Fin n → Module.End ℂ V) :
    Submodule ℂ (N →ₗ[ℂ] V) where
  carrier := {t | ∀ a b x, t (F a b x) = K a b (t x)}
  add_mem' {s t} hs ht := fun a b x => by simp [hs a b x, ht a b x]
  zero_mem' := fun a b x => by simp
  smul_mem' c t ht := fun a b x => by simp [ht a b x]

def flipL {N : Type} [AddCommGroup N] [Module ℂ N] (A : Module.End ℂ V) (T : Module.End ℂ N) :
    (N →ₗ[ℂ] V) →ₗ[ℂ] (N →ₗ[ℂ] V) where
  toFun t := A ∘ₗ t ∘ₗ T
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

end Mod

structure UF {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl : GlRel F
  unit : ∀ a b (x y : V), ⟪F a b x, y⟫_ℂ = ⟪x, F b a y⟫_ℂ

theorem uf_zero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] : UF (fun _ _ : Fin n => (0 : Module.End ℂ V)) := by
  refine ⟨?_, ?_⟩
  · intro a b c d
    simp
  · intro a b x y
    simp

theorem hwSp_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (μ : Wt n) :
    hwSp E1 E2 μ = hw (kF E1 E2) μ := rfl

def Clif {A : Type} [Ring A] (c : Fin n → Fin n → A) : Prop :=
  ∀ a b d e, c a b * c d e + c d e * c a b = if b = d ∧ a = e then 1 else 0

def spn {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A) (a b : Fin n) : A :=
  ∑ d, c a d * c d b - if a = b then algebraMap ℂ A ((n : ℂ) / 2) else 0

structure ClifMod {J : Type} [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) : Prop where
  rel : Clif c
  adj : ∀ a b, (c a b)ᴴ = c b a
  diag : ∀ a, spn c a a = Matrix.diagonal fun j => (η j a : ℂ)
  chr : ∑ j, ex (η j) = (2 : ℂ) ^ n • chR n

section Ten

variable (J : Type) [Fintype J] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

abbrev Ten (V : Type) : Type := PiLp 2 fun _ : J => V

def lf : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Ten J V) where
  toFun T :=
    { toFun := fun x => WithLp.toLp 2 fun j => T (x j)
      map_add' := fun x y => by ext j; simp
      map_smul' := fun c x => by ext j; simp }
  map_one' := by ext x j; simp
  map_mul' S T := by ext x j; simp
  map_zero' := by ext x j; simp
  map_add' S T := by ext x j; simp
  commutes' c := by ext x j; simp [Module.algebraMap_end_apply]

variable {J} (V) in

def mt (M : Matrix J J ℂ) : Module.End ℂ (Ten J V) where
  toFun x := WithLp.toLp 2 fun j => ∑ k, M j k • x k
  map_add' x y := by ext j; simp [Finset.sum_add_distrib]
  map_smul' c x := by ext j; simp [Finset.smul_sum, smul_smul, mul_comm]

variable {J} in

def dg [DecidableEq J] (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ) (a b : Fin n) :
    Module.End ℂ (Ten J V) := lf J (K a b) + mt V (spn c a b)

end Ten

end UpperTheory.RealTr
