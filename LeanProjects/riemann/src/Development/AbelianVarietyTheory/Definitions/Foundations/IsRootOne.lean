import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.H3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def JHol (X : Tower Ω ε) : Prop :=
  ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

def IsRoot (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (a b : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m

def Kum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) : Prop :=
  ∃ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M ∧ AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f ∧
    IsRoot X (l ^ n) f a b ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * (a z * b (mob (ofSL δ) z))

def Near {V : Type} (φ ψ : SL(2, ℤ) → V) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, φ δ = ψ δ

def R1 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l) (h : ℂ → ℤ_[l]) : Prop :=
  ∀ n : ℕ, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ ∧ ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
    PadicInt.toZModPow n (h (mob (ofSL δ) z) - h z) = χ δ

def Rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (b : X.Fn l) (F : ℂ → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], R1 X l (b u) (fun z => MvPolynomial.eval u (F z))

open Classical in

def cj (m : Matrix (Fin 2) (Fin 2) ℤ) (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  if h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m then h.choose else 1

def IsCoc {R : Type} [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (c : SL(2, ℤ) → MvPolynomial (Fin 2) R) : Prop :=
  (∀ γ ∈ Γ, (c γ).IsHomogeneous w) ∧
    ∀ γ ∈ Γ, ∀ δ ∈ Γ, c (γ * δ) = slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ

def IsFam (l w : ℕ) (Γ : Subgroup SL(2, ℤ)) (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  (∀ n δ, (Φ n δ).IsHomogeneous w) ∧
  (∀ n, ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
    Φ n (δ * δ') = Φ n δ + Φ n δ') ∧
  (∀ n, ∀ γ ∈ Γ, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ n (γ * δ * γ⁻¹))) (Φ n)) ∧
  ∀ n, Near (fun δ => MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (Φ (n + 1) δ)) (Φ n)

def mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (w - (i : ℕ))

def cf (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i k : Fin (w + 1)) : ℤ :=
  MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) (slP m (mon ℤ w k))

def SSPotS (S : Letter → Prop) (R : Type) [CommRing R] (N l w : ℕ) (lam : Letter → R) : Prop :=
  ∃ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' {T | S T}), FreeAlgebra.lift R lam P = 1 ∧ ∀ F ∈ Pot R w (Gam N l), ∀ T : Letter, S T →
    (opL R N l T - lam T • (1 : Module.End R (ℂ → MvPolynomial (Fin 2) R)))
      (FreeAlgebra.lift R (opL R N l) P F) ∈ Triv R w (Gam N l)

def SSBS (S : Letter → Prop) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E]
    (lam : Letter → E) : Prop :=
  ∃ P ∈ Algebra.adjoin E (FreeAlgebra.ι E '' {T | S T}), FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, S T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

def abelian₂ (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
  Submodule.span E {p | ∃ b F, Rel X l b F ∧
    p = ((1 : E) ⊗ₜ[ℤ_[l]] b, fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z))}

def deh : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval ![Polynomial.X, 1]

def cocP (Γ : Subgroup SL(2, ℤ)) (F : ℂ → MvPolynomial (Fin 2) ℂ) : Γ → Polynomial ℂ := fun γ =>
  deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I)

theorem isRoot_one (X : Tower Ω ε) (m : ℕ) (h : ((fun _ => 1 : ℂ → ℂ) : Mero) ≠ 0) :
    IsRoot X m 1 (fun _ => 1) (fun _ => 1) :=
  ⟨differentiableOn_const 1, differentiableOn_const 1, h, by simp⟩

end GlobalTheory.KZ.H3
