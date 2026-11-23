import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

def kfin (π : G n →* (U →L[ℂ] U)) : Submodule ℂ U where
  carrier := {v | ∃ S : Submodule ℂ U, FiniteDimensional ℂ S ∧ v ∈ S ∧ ∀ k, ∀ w ∈ S, π (uG k) w ∈ S}
  add_mem' := by
    rintro a b ⟨S, hS, ha, hk⟩ ⟨S', hS', hb, hk'⟩
    refine ⟨S ⊔ S', inferInstance, Submodule.add_mem_sup ha hb, fun k w hw => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    exact Submodule.add_mem_sup (hk k x hx) (hk' k y hy)
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun k w hw => by
    rw [Submodule.mem_bot] at hw ⊢; simp [hw]⟩
  smul_mem' := by
    rintro c a ⟨S, hS, ha, hk⟩
    exact ⟨S, hS, S.smul_mem c ha, hk⟩

def expG (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp ((t : ℂ) • X)).unit

@[simp] theorem coe_expG (X : Mat n) (t : ℝ) : ((expG X t : G n) : Mat n) = NormedSpace.exp ((t : ℂ) • X) := rfl

structure IsLieD (π : G n →* (U →L[ℂ] U)) (D : Mat n → Module.End ℂ (kfin π)) : Prop where
  add : ∀ X Y, D (X + Y) = D X + D Y
  smul : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X
  brk : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X
  deriv : ∀ X (v : kfin π), HasDerivAt (fun t : ℝ => π (expG X t) (v : U)) ((D X v : kfin π) : U) 0

def e1 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) - Complex.I • D (Matrix.single a b Complex.I))

def f1 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  (1 / 2 : ℂ) • (D (Matrix.single a b 1) + Complex.I • D (Matrix.single a b Complex.I))

def e2 {V : Type} [AddCommGroup V] [Module ℂ V] (D : Mat n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ V :=
  -f1 D b a

def sigK (π : G n →* (U →L[ℂ] U)) : Matrix.unitaryGroup (Fin n) ℂ →* (kfin π →ₗ[ℂ] kfin π) where
  toFun k := (π (uG k) : U →ₗ[ℂ] U).restrict (p := kfin π) (q := kfin π) (fun v ⟨S, hS, hv, hk⟩ => ⟨S, hS, hk k v hv, hk⟩)
  map_one' := by
    ext v
    simp [uG]
  map_mul' a b := by
    ext v
    simp [uG]

theorem map_mem_kfin (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U) (hA : ∀ k, A ∘L π (uG k) = π (uG k) ∘L A) {v : U}
    (hv : v ∈ kfin π) : A v ∈ kfin π := by
  obtain ⟨S, hS, hvS, hk⟩ := hv
  refine ⟨S.map (A : U →ₗ[ℂ] U), inferInstance, Submodule.mem_map_of_mem hvS, ?_⟩
  rintro k _ ⟨w, hw, rfl⟩
  have h := congrArg (fun B : U →L[ℂ] U => B w) (hA k)
  simp only [ContinuousLinearMap.comp_apply] at h
  exact ⟨π (uG k) w, hk k w hw, h⟩

def opK (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U) (hA : ∀ k, A ∘L π (uG k) = π (uG k) ∘L A) : kfin π →ₗ[ℂ] kfin π :=
  (A : U →ₗ[ℂ] U).restrict (p := kfin π) (q := kfin π) fun _ hv => map_mem_kfin π A hA hv

end GlobalTheory.CompanionTheory.GLK

end
