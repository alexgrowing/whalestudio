import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimPullTensorPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField TensorProduct

universe u

namespace GlobalTheory.SSG.DRChain

variable {C : Type} [CommRing C] {n : ℕ}

def tail (X : DRChain.{u} C n) (i : Fin (n + 1)) : X.M i →ₗ[C] X.M (Fin.last n) :=
  Fin.reverseInduction (motive := fun j ↦ X.M j →ₗ[C] X.M (Fin.last n)) LinearMap.id
    (fun j h ↦ h ∘ₗ X.f j) i

def IsTriv (X : DRChain.{u} C n) (ϖ : C) (e : ∀ i, X.M i ≃ₗ[C] (Fin n → C)) : Prop :=
  (∀ i : Fin n, (e i.succ).toLinearMap ∘ₗ X.f i = stdStep ϖ i ∘ₗ (e i.castSucc).toLinearMap) ∧
    (e 0).toLinearMap ∘ₗ X.g = (e (Fin.last n)).toLinearMap

structure IsStd [NeZero n] (X : DRChain.{u} C n) (ϖ : C) : Prop where

  free : ∀ i, Module.Free C (X.M i)

  finite : ∀ i, Module.Finite C (X.M i)

  rank : ∀ i, Module.finrank C (X.M i) = n

  coker : ∀ i : Fin n, Nonempty ((X.M i.succ ⧸ LinearMap.range (X.f i)) ≃ₗ[C] (C ⧸ Ideal.span {ϖ}))

  close_bij : Function.Bijective X.g

  close_comp : X.g ∘ₗ X.comp (Fin.last n) = ϖ • LinearMap.id

  cyclic : ∀ i, X.comp i ∘ₗ X.g ∘ₗ X.tail i = ϖ • LinearMap.id

  line_compl : ∀ i, ∃ N : Submodule C (X.M i), IsCompl (X.ω i) N

  line_free : ∀ i, Nonempty (X.ω i ≃ₗ[C] C)

  line_step : ∀ i : Fin n, (X.ω i.castSucc).map (X.f i) ≤ X.ω i.succ

  line_close : (X.ω (Fin.last n)).map X.g = X.ω 0

  exists_triv : ∃ e, X.IsTriv ϖ e

  lmPoint : ∀ e, X.IsTriv ϖ e → ∃ P : LMPoint C ϖ n,
    ∀ i : Fin (n + 1), (X.ω i).map (e i).toLinearMap = P.ℓ ⟨(i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩

end GlobalTheory.SSG.DRChain

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.IsMatUnitAt (D : Datum p) {C : Type} [CommRing C] (χ : 𝓞 D.F →+* C) (ε : C ⊗[ℤ] D.O) : Prop :=
  IsIdempotentElem ε ∧ ∃ ψ : C ⊗[ℤ] D.O →ₐ[C] Matrix (Fin D.m) (Fin D.m) C, Function.Surjective ψ ∧
    (∀ x : 𝓞 D.F, ψ (1 ⊗ₜ algebraMap (𝓞 D.F) D.O x) = algebraMap C _ (χ x)) ∧
    ψ ε = Matrix.single ⟨0, D.m_pos⟩ ⟨0, D.m_pos⟩ 1

instance Datum.neZero_n (D : Datum p) : NeZero D.n := ⟨Nat.one_le_iff_ne_zero.1 D.n_pos⟩

end GlobalTheory.UPel.HT

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

def DRChainStdSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), D.a = 1 →
    ∀ (i : Fin D.a) (w : Ideal (𝓞 D.F)), IsPlaceOf b i w →
    ∀ (C : Type) [CommRing C] [IsLocalRing C] (σ : R →+* C) (o : Obj b N (spMap σ)) (c : HTIw o w)
      (ε : C ⊗[ℤ] D.O), D.IsMatUnitAt (σ.comp (b.t i)) ε →
    ∀ (a : 𝓞 D.F) (ha : a ∈ w), a ∉ w ^ 2 → (c.drChain i ε ha).IsStd (σ (b.t i a))

end GlobalTheory.IwLevel
