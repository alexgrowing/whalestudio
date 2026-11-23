import Mathlib
import GroundTheory.AutomorphicForms.WhittakerLSpace
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.HighestDerivProd
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsInvForm {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ (∀ v, v ≠ 0 → 0 < (B v v).re) ∧ ∀ g v w, B (ρ g v) (ρ g w) = B v w

def aDiag (N m : ℕ) (z : kˣ) : GL (Fin N) k :=
  ⟨diagonal fun i => if (i : ℕ) < m then (z : k) else 1, diagonal fun i => if (i : ℕ) < m then ((z⁻¹ : kˣ) : k) else 1,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp⟩

def BesselSum : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsUnitarisable π →
    ∃ Q : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, (∀ v w, Q w v = starRingEnd ℂ (Q v w)) ∧ (∀ v, 0 ≤ (Q v v).re) ∧
      (∀ v, Q v v = 0 ↔ v ∈ twKer π (unipB k (Fin N)) (whitChar ψ N)) ∧
      ∀ (m : ℕ), 1 ≤ m → m < N → ∀ z : kˣ, nabs k z < 1 → ∀ v,
        Summable fun i : ℕ => (nabs k z ^ (i * m * (N - m - 1)))⁻¹ *
          (Q (π (aDiag k N m (z ^ i)) v) (π (aDiag k N m (z ^ i)) v)).re

def OpenCell : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (r m : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W)
    (ω : kˣ →* ℂˣ), IsSmooth A → IsSmooth x → IsGenericFor ψ A → IsGenericFor ψ x → HasCentralChar x ω →
    ∀ z : kˣ, nabs k z < 1 → ∃ f f₀, f₀ ∉ twKer (prod₂ A x) (unipB k (Fin (r + m))) (whitChar ψ (r + m)) ∧
      ∃ i₀ : ℕ, ∀ i ≥ i₀, prod₂ A x (aDiag k (r + m) m (z ^ i)) f -
        (((Real.sqrt (nabs k z) : ℝ) : ℂ) ^ (i * m * r) * (ω z : ℂ) ^ i) • f₀ ∈
          twKer (prod₂ A x) (unipB k (Fin (r + m))) (whitChar ψ (r + m))

def ExpLow : Prop :=
  ∀ (r m : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Representation ℂ (GL (Fin r) k) V) (x : Representation ℂ (GL (Fin m) k) W) (ω : kˣ →* ℂˣ) (s : ℝ), 1 ≤ r → 1 ≤ m →
    IsSmooth A → IsSmooth x → IsGeneric (prod₂ A x) → IsUnitarisable (prod₂ A x) → HasCentralChar x ω →
    (∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ ((m : ℝ) * s)) → -1 / 2 < s

def ExpBound : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), (prodIrr x hd).IsIrreducible → IsUnitarisable (prodIrr x hd) →
    IsGeneric (prodIrr x hd) → ∀ (j : Fin h) (ω : kˣ →* ℂˣ) (s : ℝ), 0 < (x j).1 → HasCentralChar (x j).rep ω →
    (∀ z, ‖(ω z : ℂ)‖ = nabs k z ^ (((x j).1 : ℝ) * s)) → |s| < 1 / 2

def ThmT : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) → IsReduced Z →
    ∀ ξ : (Matrix (Fin n) (Fin n) k × (Fin n → k) → ℂ) →ₗ[ℂ] ℂ,
      (∀ f ∈ supportedIn (Set.univ : Set (Matrix (Fin n) (Fin n) k × (Fin n → k))),
        (∀ p, (∀ a ∈ Z, a * p.1 = p.1 * a) → f p = 0) → ξ f = 0) →
      (∀ g : GL (Fin n) k, (∀ a ∈ Z, a * g.val = g.val * a) →
        ∀ f ∈ supportedIn (Set.univ : Set (Matrix (Fin n) (Fin n) k × (Fin n → k))),
          ξ (fun p => f (g.val * p.1 * g⁻¹.val, g.val *ᵥ p.2)) = ξ f) →
      ∀ f ∈ supportedIn {p : Matrix (Fin n) (Fin n) k × (Fin n → k) | p.2 ≠ 0}, ξ f = 0

def ThmA : Prop :=
  ∀ (n : ℕ) (Λ : (GL (Fin (n + 1)) k → ℂ) →ₗ[ℂ] ℂ),
    (∀ p ∈ Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)), Λ (fun g => f (p * g * p⁻¹)) = Λ f) →
    ∀ p, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)), Λ (fun g => f (p * g * p⁻¹)) = Λ f

def ThmB : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) k) V),
    IsSmooth π → π.IsIrreducible → ∀ B, IsInvForm π B → ∀ β : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ,
    (∀ p ∈ Mir k n, ∀ v w, β (π p v) (π p w) = β v w) → ∃ c : ℂ, ∀ v w, β v w = c * B v w

def DerivTop : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n h : ℕ) (π : GRep k (n + h)), 1 ≤ h → IsSmooth π.ρ →
    π.ρ.IsIrreducible → IsUnitarisable π.ρ → Nontrivial (derivB ψ h π).V →
    (∀ (n' h' : ℕ) (e : n + h = n' + h'), h < h' → Subsingleton (derivB ψ h' (π.cast e)).V) →
    ((derivB ψ h π).tw ((1 - (h : ℝ)) / 2)).ρ.IsIrreducible ∧ IsUnitarisable ((derivB ψ h π).tw ((1 - (h : ℝ)) / 2)).ρ

def DerivPos : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n i : ℕ) (π : GRep k (n + i)), 1 ≤ i → IsSmooth π.ρ →
    π.ρ.IsIrreducible → IsUnitarisable π.ρ →
    (∃ (n' h' : ℕ) (e : n + i = n' + h'), i < h' ∧ Nontrivial (derivB ψ h' (π.cast e)).V) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin n) k) W) (ω : kˣ →* ℂˣ), Nontrivial W →
      IsSubquotient σ ((derivB ψ i π).tw ((1 - (i : ℝ)) / 2)).ρ → HasCentralChar σ ω →
      ∀ z : kˣ, nabs k z < 1 → ‖(ω z : ℂ)‖ < 1

def BernAt : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ → IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible

end PositivityTheory.RgUd
