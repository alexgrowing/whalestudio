import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

abbrev jacU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) : Submodule ℂ V :=
  jacSub ρ (fun u => IsUniM (u : GL (Fin n) L))

def KInvForm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
      ∀ v₀ ∈ fixed ρ K, v₀ ≠ 0 → ∃ l : Module.Dual ℂ V, (∀ k ∈ K, l ∘ₗ ρ k = l) ∧ l v₀ = 1

def KUFacts : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) ∧ IwU σ n ≤ KU σ n ∧
      ∃ t : GU σ n, IsDiagM (t : GL (Fin n) L) ∧ IsStrictDom (t : GL (Fin n) L)

def SphCompare : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V)
      (α : Fin (n / 2) → ℂˣ) (v₀ : V), IsSatVecU ϖ q ρ v₀ α → ∀ l : Module.Dual ℂ V, (∀ k ∈ KU σ n, l ∘ₗ ρ k = l) →
      ∀ g : GU σ n, (Nat.card {c : GU σ n ⧸ KU σ n //
          (c.out : GU σ n) ∈ DoubleCoset.doubleCoset g (KU σ n : Set (GU σ n)) (KU σ n)} : ℂ) * l (ρ g v₀) =
        SatU ϖ q (dosetInd ℂ (KU σ n) g) (fun i => (α i : ℂ)) * l v₀

def SatPowNonvan : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n), IsDiagM (t : GL (Fin n) L) →
      IsStrictDom (t : GL (Fin n) L) → ∀ j₀ : ℕ, ∃ j ≥ j₀, SatU ϖ q (dosetInd ℂ (KU σ n) (t ^ j)) (fun i => (α i : ℂ)) ≠ 0

def JacNeU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → HasSatU ϖ q ρ α →
    ∃ y : V, y ∉ jacU ρ ∧ ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ

def EigU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1

def EqFormU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ (ξ : GU σ n → ℂ) (y : V), y ∉ jacU ρ →
    (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y - ξ t • y ∈ jacU ρ) →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1) →
    ∃ lam : Module.Dual ℂ V, (∀ x ∈ jacU ρ, lam x = 0) ∧ lam ≠ 0 ∧
      ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ∀ v, lam (ρ t v) = ξ t * lam v

def CharU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → ∀ (ξ : GU σ n → ℂ) (y : V), y ∉ jacU ρ →
    (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y - ξ t • y ∈ jacU ρ) →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1) →
    ∃ β : Fin (n / 2) → ℂˣ, ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ξ t = chiDeltaU q (fun i => (β i : ℂ)) t

def BorelSplitU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) →
    ∀ b : GU σ n, IsBorelU b → ∃ t u : GU σ n, IsDiagM (t : GL (Fin n) L) ∧ IsUniM (u : GL (Fin n) L) ∧ b = t * u

def FrobU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → HasSatU ϖ q ρ α →
    ∀ (β : Fin (n / 2) → ℂˣ) (lam : Module.Dual ℂ V), (∀ x ∈ jacU ρ, lam x = 0) → lam ≠ 0 →
      (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ∀ v, lam (ρ t v) = chiDeltaU q (fun i => (β i : ℂ)) t * lam v) →
      GlobalTheory.LGrp.WeylConjU α β ∧ ∃ f : V →ₗ[ℂ] psSpaceU σ q β, Function.Injective f ∧
        ∀ (g : GU σ n) (v : V), f (ρ g v) = psFunU σ q β g (f v)

def SwapStepU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) →
    ∀ (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val + 1 = j.val → ‖(χ i : ℂ) / χ j‖ < 1 →
    ∀ f : V →ₗ[ℂ] psSpaceU σ q χ, Function.Injective f → (∀ (g : GU σ n) (v : V), f (ρ g v) = psFunU σ q χ g (f v)) →
      ∃ f' : V →ₗ[ℂ] psSpaceU σ q (χ ∘ Equiv.swap i j), Function.Injective f' ∧
        ∀ (g : GU σ n) (v : V), f' (ρ g v) = psFunU σ q (χ ∘ Equiv.swap i j) g (f' v)

def InvStepU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) →
    ∀ (χ : Fin (n / 2) → ℂˣ) (j : Fin (n / 2)), j.val + 1 = n / 2 → ‖(χ j : ℂ)‖ < 1 →
    ∀ f : V →ₗ[ℂ] psSpaceU σ q χ, Function.Injective f → (∀ (g : GU σ n) (v : V), f (ρ g v) = psFunU σ q χ g (f v)) →
      ∃ f' : V →ₗ[ℂ] psSpaceU σ q (Function.update χ j (χ j)⁻¹), Function.Injective f' ∧
        ∀ (g : GU σ n) (v : V), f' (ρ g v) = psFunU σ q (Function.update χ j (χ j)⁻¹) g (f' v)

def ChamberU : Prop :=
  SwapStepU → InvStepU →
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) →
    ∀ (α χ : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.WeylConjU α χ →
    ∀ f : V →ₗ[ℂ] psSpaceU σ q χ, Function.Injective f → (∀ (g : GU σ n) (v : V), f (ρ g v) = psFunU σ q χ g (f v)) →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧
      ∃ f' : V →ₗ[ℂ] psSpaceU σ q β, Function.Injective f' ∧
        ∀ (g : GU σ n) (v : V), f' (ρ g v) = psFunU σ q β g (f' v)

end PositivityTheory.SphericalProduct

end
