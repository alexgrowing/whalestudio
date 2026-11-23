import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.StepDown

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in

theorem supp_const (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ)
    (h : L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) ≠ 0) : ∀ a b, d a = d b := by
  have hcons : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ = d ⟨j + 1, hj⟩ := by
    intro j hj
    rcases lt_trichotomy (d ⟨j, by omega⟩) (d ⟨j + 1, hj⟩) with hlt | heq | hgt
    · exact absurd (step_up i hi hψ h0 τ π φ hφ L hL x d ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl hlt) h
    · exact heq
    · exact absurd (step_down i hi hψ τ hτ π φ hφ L hL x d ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl hgt) h
  have hall : ∀ (j : ℕ) (hj : j < n), d ⟨j, hj⟩ = d ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih => intro hj; rw [← hcons j hj, ih (by omega)]
  intro a b
  exact (hall a.val a.isLt).trans (hall b.val b.isLt).symm

end DiscreteGroups.sglob.DzRed
