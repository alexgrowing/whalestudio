import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ ReciprocityTheory.Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) : X.Khat l :=
  Classical.epsilon fun b : X.Khat l => AdicCompletion.eval (idl l) (X.Kl l) n b = a

open Classical in

def clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (w : X.K) : X.Khat l :=
  if h : w ≠ 0 then liftK X l n (X.cls l n (Units.mk0 w h)) else 0

def liftSL (M : ℕ) (g : SL(2, ZMod M)) : SL(2, ℤ) :=
  Classical.epsilon fun γ : SL(2, ℤ) => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = g

open Classical in

def clsB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ))
    (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  let M : ℕ := l ^ (r + n) * N
  haveI : NeZero M := ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (NeZero.ne N)⟩
  let f : X.Fn l := fun u => (u 0) ^ (k - 2) • clsK X l n (wk4 X l n r N x c d σ)
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Finset.univ.filter (fun γ : SL(2, ZMod M) =>
      γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))),
    X.act l ((g r₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f

def repC (l : ℕ) [Fact l.Prime] (r : ℕ) (x : (ZMod (l ^ r))ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => cycMod (F := ℚ) (Ω := Ω) l r s = x

def Yk4 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ) : Fin 2 → Qbar l :=
  GlobalTheory.Ord2.mat W (repC l r y) *ᵥ
    pr (clsB X l n r N x c d k g ((repC l r y)⁻¹ * s * repC l r (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)))

def Zk4 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (r : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  limUnder atTop fun n : ℕ => Yk4 X l pr W n r N x c d k g s y 1

def chik4 (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ((((y : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

def yk4 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k e : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (s : Ω ≃ₐ[ℚ] Ω) : Fin 2 → Qbar l :=
  limUnder atTop fun r : ℕ => GlobalTheory.KA.spec (chik4 l e ψ r) (Yk4 X l pr W r r N x c d k g) s

def nuk4 {l : ℕ} [Fact l.Prime] (W : GlobalTheory.Ord2.R2 Ω l) (A : ValuationSubring Ω) : (Ω ≃ₐ[ℚ] Ω) →* (Qbar l)ˣ :=
  Classical.epsilon fun ν : (Ω ≃ₐ[ℚ] Ω) →* (Qbar l)ˣ => ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) = GlobalTheory.Ord2.mat W s 1 1

end GlobalTheory.K4
