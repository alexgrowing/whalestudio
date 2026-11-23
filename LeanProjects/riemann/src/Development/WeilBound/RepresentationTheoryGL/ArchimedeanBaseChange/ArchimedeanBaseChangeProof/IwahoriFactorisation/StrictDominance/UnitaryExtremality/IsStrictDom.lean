import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

noncomputable section

open GlobalTheory.PRep Formalism.UG NumberField IsDedekindDomain PositivityTheory.Lbc
open scoped Pointwise

namespace PositivityTheory.SphericalProduct

section Lat

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def latK (n k : ℕ) : Set (Fin n → L) :=
  {x | ∀ i : Fin n, if i.val < k then Valued.v (x i) ≤ 1 else Valued.v (x i) < 1}

def IwGL (n : ℕ) : Subgroup (GL (Fin n) L) :=
  ⨅ k : Fin (n + 1), (MulAction.stabilizer (LinearMap.GeneralLinearGroup L (Fin n → L)) (latK L n k)).comap
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n) L ≃* _).toMonoidHom

variable {L}

def IsDiagM {n : ℕ} (g : GL (Fin n) L) : Prop := ∀ i j : Fin n, i ≠ j → (g : Matrix (Fin n) (Fin n) L) i j = 0

def IsUniM {n : ℕ} (g : GL (Fin n) L) : Prop :=
  (∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) L) i j = 0) ∧ ∀ i : Fin n, (g : Matrix (Fin n) (Fin n) L) i i = 1

def IsStrictDom {n : ℕ} (g : GL (Fin n) L) : Prop :=
  ∀ i j : Fin n, i < j → ordL ((g : Matrix (Fin n) (Fin n) L) j j) < ordL ((g : Matrix (Fin n) (Fin n) L) i i)

end Lat

def jacSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (N : G → Prop) :
    Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ u, N u ∧ ∃ v, y = ρ u v - v}

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def IwU (σ : L →+* L) (n : ℕ) : Subgroup (GU σ n) := (IwGL L n).subgroupOf (GU σ n)

def ExtremeU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LFun.HasSatU ϖ q ρ α →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧
      ∃ f : V →ₗ[ℂ] GlobalTheory.LFun.psSpaceU σ q β, Function.Injective f ∧
        ∀ (g : GU σ n) (v : V), f (ρ g v) = GlobalTheory.LFun.psFunU σ q β g (f v)

def ExpU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LFun.HasSatU ϖ q ρ α →
    ∀ (ξ : GU σ n → ℂ) (y : V), y ∉ jacSub ρ (fun u => IsUniM (u : GL (Fin n) L)) →
      (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y - ξ t • y ∈ jacSub ρ (fun u => IsUniM (u : GL (Fin n) L))) →
      (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1) →
      ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧
        ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ξ t = chiDeltaU q (fun i => (β i : ℂ)) t

end U

section GeneralLinearIntegers

def ExpGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (B : Multiset ℂˣ), IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LFun.HasSatGL w ρ B →
    ∀ (ξ : GL (Fin n) (w.adicCompletion E) → ℂ) (y : V), y ∉ jacSub ρ IsUniM →
      (∀ t, IsDiagM t → ρ t y - ξ t • y ∈ jacSub ρ IsUniM) →
      (∀ k ∈ GlobalTheory.LFun.KGL w n, IsDiagM k → ξ k = 1) →
      ∃ β : Fin n → ℂˣ, Finset.univ.val.map β = B ∧ ∀ t, IsDiagM t → ξ t = chiDelta E w (fun i => (β i : ℂ)) t

end GeneralLinearIntegers

end PositivityTheory.SphericalProduct

end
