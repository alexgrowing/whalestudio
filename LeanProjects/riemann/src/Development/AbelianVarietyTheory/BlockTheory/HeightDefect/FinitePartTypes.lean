import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def kFin {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  sSup {W | FiniteDimensional ℂ W ∧ IsKStableOn ε σ W}

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)

structure IsGKMap {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)) : Prop where

  aut : ∀ v, IsAutFunSm θ V (T v)

  mapK : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
    ∀ v w : kFin ε σ, (w : H) = σ (P * g * P⁻¹) v → T w = rTr V (atTau θ V τ g) (T v)

  mapLie : ∀ X ∈ lieAt V τ, ∀ v w : kFin ε σ,
    HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0 →
      T w = Rder θ V τ X (T v)

def finPartOfType (S : SPar) : Submodule ℂ (GA D V → ℂ) :=
  sSup {W | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
    (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    IsEnum S lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ IsDS ε lam σ ∧ IsUnit P ∧
      Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ ∧ IsGKMap θ V τ ε σ P T ∧ W = LinearMap.range T}

def HasTypeAt (S : SPar) (φ : GA D V → ℂ) : Prop :=
  ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ ψ ∈ finPartOfType θ V τ S, ∀ x ∈ C, ‖φ x - ψ x‖ < δ

def IsCompatibleThetaType {X : ThetaX D} (T : ThetaTied D X) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V : HSp D, V.SigOK → ∀ (S : D.what₂.Tau → SPar) (F : X.AF V),
    F ∈ X.typ V S ↔ ∀ τ, HasTypeAt θ V τ (S τ) (T.ev V F)

theorem HasTypeAt.of_mem {S : SPar} {φ : GA D V → ℂ} (h : φ ∈ finPartOfType θ V τ S) : HasTypeAt θ V τ S φ :=
  fun _ _ δ hδ => ⟨φ, h, fun x _ => by simpa using hδ⟩

def typeSub (S : SPar) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | HasTypeAt θ V τ S φ}
  zero_mem' := HasTypeAt.of_mem θ V τ (Submodule.zero_mem _)
  add_mem' := by
    intro a b ha hb C hC δ hδ
    obtain ⟨ψ, hψ, h1⟩ := ha C hC (δ / 2) (by linarith)
    obtain ⟨ψ', hψ', h2⟩ := hb C hC (δ / 2) (by linarith)
    refine ⟨ψ + ψ', Submodule.add_mem _ hψ hψ', fun x hx => ?_⟩
    have e : (a + b) x - (ψ + ψ') x = (a x - ψ x) + (b x - ψ' x) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    have := norm_add_le (a x - ψ x) (b x - ψ' x)
    linarith [h1 x hx, h2 x hx]
  smul_mem' := by
    intro c a ha C hC δ hδ
    have hc : 0 < ‖c‖ + 1 := by positivity
    obtain ⟨ψ, hψ, h1⟩ := ha C hC (δ / (‖c‖ + 1)) (div_pos hδ hc)
    refine ⟨c • ψ, Submodule.smul_mem _ c hψ, fun x hx => ?_⟩
    have e : (c • a) x - (c • ψ) x = c * (a x - ψ x) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, norm_mul]
    have h2 := (lt_div_iff₀ hc).1 (h1 x hx)
    nlinarith [norm_nonneg c, norm_nonneg (a x - ψ x)]

theorem HasTypeAt.eq_zero_of_not_good {S : SPar} (hS : ∀ p q, ¬ GoodPar V.rank p q S) {φ : GA D V → ℂ}
    (h : HasTypeAt θ V τ S φ) : φ = 0 := by
  have hb : finPartOfType θ V τ S = ⊥ := by
    rw [finPartOfType, sSup_eq_bot]
    rintro W ⟨H, _, _, σ, lam, ε, P, T, h1, h2, -⟩
    exact (hS _ _ ⟨lam, ε, h1, h2, rfl, rfl⟩).elim
  funext x
  by_contra hx
  obtain ⟨ψ, hψ, h1⟩ := h {x} isCompact_singleton ‖φ x‖ (norm_pos_iff.2 hx)
  rw [hb, Submodule.mem_bot] at hψ
  have := h1 x rfl
  simp [hψ] at this

end GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes

end
