import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ProdFam

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Bi

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']

variable (k ι κ E'') in

def biD : (Finset ι × Finset κ → E'') →ₗ[k] (Finset ι × Finset κ → E'') :=
  LinearMap.pi fun x =>
    (∑ i ∈ x.1, GlobalTheory.cubeSign x.1 i • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1.erase i, x.2)) +
      ((-1 : ℤ) ^ (x.1.card + 1)) •
        ∑ j ∈ x.2, GlobalTheory.cubeSign x.2 j • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1, x.2.erase j)

def bicechC (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (n : ℤ) :
    Submodule k (Finset ι × Finset κ → E'') :=
  Submodule.pi Set.univ fun x =>
    if x.1.Nonempty ∧ x.2.Nonempty ∧ ((x.1.card + x.2.card : ℕ) : ℤ) = n + 2 then Submodule.map₂ μ (A x.1) (B x.2) else ⊥

def bicech (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') :
    Cx k (Finset ι × Finset κ → E'') :=
  ⟨bicechC μ A B, biD k ι κ E''⟩

def boxC (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset ι × Finset κ → E'' :=
  fun x => μ (a x.1) (b x.2)

variable (k ι κ E'') in
open Classical in

def crossL : (Finset ι × Finset κ → E'') →ₗ[k] (Finset (ι ×ₗ κ) → E'') :=
  LinearMap.pi fun u => ∑ j ∈ u,
    if Set.InjOn fstL (↑(u.filter (· ≤ j)) : Set (ι ×ₗ κ)) ∧ Set.InjOn sndL (↑(u.filter (j ≤ ·)) : Set (ι ×ₗ κ)) then
      (idxSign fstL (u.filter (· ≤ j)) * idxSign sndL (u.filter (j ≤ ·))) •
        LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') ((u.filter (· ≤ j)).image fstL, (u.filter (j ≤ ·)).image sndL)
    else 0

end Bi

example : bicech (k := ℚ) (ι := Unit) (κ := Unit) (LinearMap.mul ℚ ℚ) (fun _ => ⊤) (fun _ => ⊤) =
    ⟨bicechC (LinearMap.mul ℚ ℚ) (fun _ => ⊤) (fun _ => ⊤), biD ℚ Unit Unit ℚ⟩ := rfl

example (a : Finset Unit → ℚ) (b : Finset Unit → ℚ) : boxC (LinearMap.mul ℚ ℚ) a b ({()}, {()}) = a {()} * b {()} := rfl

end GlobalTheory.PD
