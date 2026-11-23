import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.HoweR

section Gl

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def IsGl (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ a b c d, F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)

def negT (F : ι → ι → Module.End ℂ M) : ι → ι → Module.End ℂ M := fun a b => -F b a

def cas (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b, if s a = s b then F a b * F b a else 0

def qop (F : ι → ι → Module.End ℂ M) (α β : ℂ) (a b : ι) : Module.End ℂ M :=
  ∑ c, F a c * F c b - α • F a b - if a = b then β • 1 else 0

def UnitOn (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) : Prop :=
  FiniteDimensional ℂ U ∧ (∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) ∧
    ∃ ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) ∧ (∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) ∧
      ∀ a b, s a = s b → ∀ x ∈ U, ∀ y ∈ U, ip (F a b x) y = ip x (F b a y)

def LocU (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ t : Finset M, ∃ U : Submodule ℂ M, (∀ x ∈ t, x ∈ U) ∧ UnitOn s F U

end Gl

section Act

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def units (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Ix p q → Ix p q → Module.End ℂ V := fun a b => act (Eab a b)

def Stab (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Prop := ∀ Z, ∀ y ∈ N, act Z y ∈ N

def Good (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  IsLieAct act ∧ (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) ∧ LocU (fun a : Ix p q => a.isLeft) (units act)

def QuadMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (α β α' β' : ℂ) (N N' : Submodule ℂ V) : Prop :=
  ∀ a b, ∀ v ∈ N', qop (units act) α β a b v ∈ N ∧ qop (negT (units act)) α' β' a b v ∈ N

def AdmMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) → hwSub act μ ≤ U ⊔ C

def CycMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∃ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ ∧ genSub act {v} ⊔ C = ⊤ ∧ hwSub act μ ≤ Submodule.span ℂ {v} ⊔ C

def Pack (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  Good act ∧ Stab act C ∧ (∃ α β α' β' : ℂ, QuadMod act α β α' β' C ⊤) ∧ AdmMod act C ∧ CycMod act C

end Act

def coinv (P Q R S : ℕ) (x : ℂ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Formalism.BasicNotions.TH.Pol P Q R S), g = fockAct1 P Q R S X f - (x * X.trace) • f}

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

def actAt {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) : Mat p q →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) ∘ₗ a

theorem actAt_apply {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (Z : Mat p q) :
    actAt w a Z = atPl w (a Z) := rfl

def tensAll (H : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∀ w, f w ∈ H w) ∧ y = PiTensorProduct.tprod ℂ f}

def tensAny (C : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∃ w, f w ∈ C w) ∧ y = PiTensorProduct.tprod ℂ f}

end Tensor

def HoweAlg {T : Type} {R S : T → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, (∀ w, Stab (a w) (N k)) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → N ≠ ⊤ → (∀ w, Stab (a w) N') → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

example : IsGl (fun _ _ : Fin 2 => (0 : Module.End ℂ ℂ)) ∧ cas (fun _ : Fin 2 => true) (fun _ _ => (0 : Module.End ℂ ℂ)) = 0 := by
  refine ⟨fun a b c d => by simp, by simp [cas]⟩

end GlobalTheory.HoweR

end
