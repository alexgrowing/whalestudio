import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ProdFam

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']
  [AddCommGroup E''] [Module k E'']

def diagL : ι → ι ×ₗ ι := fun i => toLex (i, i)

def cupμ (μ : E →ₗ[k] E' →ₗ[k] E'') (x : Finset ι → E) (y : Finset ι → E') : Finset ι → E'' :=
  pullIdx diagL (crossC μ x y)

def IsDualBasis [Fintype ι] (β : E →ₗ[k] E' →ₗ[k] k) (A : Finset ι → Submodule k E) (A' : Finset ι → Submodule k E') (N : ℤ)
    {m : ℕ} (p : Fin m → ℤ) (e : Fin m → Finset ι → E) (f : Fin m → Finset ι → E') : Prop :=
  (∀ i, e i ∈ (cech A).Z (p i) ∧ f i ∈ (cech A').Z (N - p i)) ∧
  (∀ i j, cupPair β (e i) (f j) = if i = j then 1 else 0) ∧
  ∀ (q : ℤ), ∀ x ∈ (cech A).Z q, ∃ c : Fin m → k, x - ∑ i ∈ Finset.univ.filter (fun i => p i = q), c i • e i ∈ (cech A).B q

def diagC {m : ℕ} (μ : E' →ₗ[k] E →ₗ[k] E'') (e : Fin m → Finset ι → E) (f : Fin m → Finset ι → E') : Finset (ι ×ₗ ι) → E'' :=
  ∑ i, crossC μ (f i) (e i)

end GlobalTheory.PD
