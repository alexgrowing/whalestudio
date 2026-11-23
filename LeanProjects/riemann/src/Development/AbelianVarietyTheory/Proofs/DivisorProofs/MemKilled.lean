import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMaps

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CapKilled

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def ktype (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W}
  zero_mem' g := by
    have e : (fun k : Kinf E a => (cptRep E a k 0).1 g) = 0 := by funext k; simp
    rw [e]; exact W.zero_mem
  add_mem' {ψ ψ'} h h' g := by
    have e : (fun k : Kinf E a => (cptRep E a k (ψ + ψ')).1 g) =
        (fun k : Kinf E a => (cptRep E a k ψ).1 g) + fun k : Kinf E a => (cptRep E a k ψ').1 g := by
      funext k; simp
    rw [e]
    exact W.add_mem (h g) (h' g)
  smul_mem' c ψ h g := by
    have e : (fun k : Kinf E a => (cptRep E a k (c • ψ)).1 g) = c • fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; simp
    rw [e]
    exact W.smul_mem c (h g)

variable (E a) in

def killed (q : (E →+* ℂ) → ℂ → Polynomial ℂ) : Submodule ℂ (Sm E a) :=
  ⨅ τ, ⨅ u, LinearMap.ker (Polynomial.aeval (cap τ u) (q τ u))

variable (E a) in

def space (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ))
    (q : (E →+* ℂ) → ℂ → Polynomial ℂ) : Submodule ℂ (Sm E a) :=
  leftInv E a ⊓ fixL E a L ⊓ ktype E a W ⊓ killed E a q ⊓ tame E a

theorem mem_killed {q : (E →+* ℂ) → ℂ → Polynomial ℂ} {ψ : Sm E a} :
    ψ ∈ killed E a q ↔ ∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0 := by
  simp [killed, Submodule.mem_iInf]

theorem mem_space {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {q : (E →+* ℂ) → ℂ → Polynomial ℂ} {ψ : Sm E a} :
    ψ ∈ space E a L W q ↔ (∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g) ∧ (∀ k ∈ L, finRep E a k ψ = ψ) ∧
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W) ∧
      (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) ∧ ψ ∈ tame E a := by
  rw [space, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, mem_killed]
  exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩

end GlobalTheory.CapKilled

end
