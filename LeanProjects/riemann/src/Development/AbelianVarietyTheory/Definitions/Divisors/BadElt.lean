import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadCount

def EmbReg {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
    (H : Subgroup Γ) (n : ℕ) : Prop :=
  ∃ j : V →ₗ[K] (Fin n → MonoidAlgebra K H), Function.Injective j ∧
    ∀ (h : H) (v : V) (i : Fin n), j (ρ h v) i = MonoidAlgebra.single h 1 * j v i

def eig {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
    (H : Subgroup Γ) (lam : H →* Kˣ) : Submodule K V :=
  ⨅ h : H, LinearMap.ker (ρ h - ((lam h : Kˣ) : K) • LinearMap.id)

theorem mem_eig {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V)
    (H : Subgroup Γ) (lam : H →* Kˣ) (v : V) : v ∈ eig ρ H lam ↔ ∀ h : H, ρ h v = ((lam h : Kˣ) : K) • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

example {K Γ : Type} [Field K] [Group Γ] (H : Subgroup Γ) : EmbReg (1 : Representation K Γ (Fin 0 → K)) H 0 :=
  ⟨0, fun _ _ _ => Subsingleton.elim _ _, fun _ _ i => i.elim0⟩

variable (D : D7)

open Classical in

def badElt (k : Fin 2) (S : Finset (Tup D k)) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0g D.nd =>
    if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0

def IsWhit (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ)
    (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) : Prop :=
  (∀ kv, ψ kv ≠ 1) ∧
  (∀ g : G0g D.nd, g ∈ P ↔ ∀ kv, IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) ∧
  ∀ g : P, ((lam g : ℂˣ) : ℂ) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ kv (∑ i ∈ Finset.range (D.R.r - 1),
    entN ((g : G0g D.nd) kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i (i + 1))

def IsHalf (k : Fin 2) (H : Subgroup (G0g D.nd)) : Prop :=
  ∀ g : G0g D.nd, g ∈ H ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k →
    IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))

def IsSplit {Γ G : Type} [Group Γ] [Group G] (π : Γ →* G) (ι : G →* Γ) : Prop :=
  (∀ g, π (ι g) = g) ∧ ∀ g γ, π γ = 1 → ι g * γ = γ * ι g

end GlobalTheory.BadCount
