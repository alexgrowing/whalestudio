import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import Formalism.LocalToGlobal.AdelicCompactOpens.GLintCompactOpen

namespace Formalism.L2.Props

open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut

section

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def CompAtUnique : Prop :=
  ∀ (χ : Host.HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion L⁺)ˣ →* ℂˣ),
    IsCompAt χ s ξ → IsCompAt χ s ξ' → ξ = ξ'

def CompAtExists : Prop :=
  ∀ (χ : Host.HChar L) (s : SplitPlace L), ∃ ξ, IsCompAt χ s ξ

def DualUnique : Prop :=
  ∀ a b b' : AlgWt L n, a.IsDual b → a.IsDual b' → b.Iso b'

def UniCharMulNG : Prop :=
  ∀ (s : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ),
    IsPsi0 s ψ₀ → (∀ u : (s.v.adicCompletion L⁺)ˣ, Valued.v ((u : s.v.adicCompletion L⁺) - 1) < 1 → ξ u = 1) →
    ∀ (g h : GL (Fin n) (s.v.adicCompletion L⁺)) (ug uh ugh : (s.v.adicCompletion L⁺)ˣ), UniRT s r g → UniRT s r h →
      (ug : s.v.adicCompletion L⁺) = detDD s r g → (uh : s.v.adicCompletion L⁺) = detDD s r h →
      (ugh : s.v.adicCompletion L⁺) = detDD s r (g * h) →
      ψ₀ (supDiag s r (g * h)) * (ξ ugh : ℂ) = (ψ₀ (supDiag s r g) * (ξ ug : ℂ)) * (ψ₀ (supDiag s r h) * (ξ uh : ℂ))

def DualExists : Prop := ∀ a : AlgWt L n, ∃ b, a.IsDual b

def HWUnique : Prop :=
  ∀ (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ), a.HWAt τ lam → a.HWAt τ lam' → lam = lam'

def HWExists : Prop := ∀ (a : AlgWt L n) (τ : L →+* ℂ), ∃ lam, a.HWAt τ lam

variable {L n}

theorem uniR_of_uniRT {s : SplitPlace L} {r : ℕ} {h : GL (Fin n) (s.v.adicCompletion L⁺)} (hh : UniRT s r h) :
    UniR r h := by
  unfold UniR
  refine ⟨?_, hh.2⟩
  unfold ParaR
  obtain ⟨⟨g, hg⟩, hlow⟩ := hh.1
  refine ⟨?_, ?_, hlow⟩
  · intro a b
    rw [← hg]
    exact (g.val a b).2
  · intro a b
    rw [← hg, ← map_inv]
    exact (g⁻¹.val a b).2

theorem uniCharMul_ng (H : UniCharMul) : UniCharMulNG L n := by
  unfold UniCharMul at H
  intro s r ψ₀ ξ hψ hξ g h ug uh ugh hg hh hug huh hugh
  exact @H (s.v.adicCompletion L⁺) _ _ n r ψ₀ ξ hψ.1 hξ g h ug uh ugh (uniR_of_uniRT hg)
    (uniR_of_uniRT hh) hug huh hugh

end

end Formalism.L2.Props
