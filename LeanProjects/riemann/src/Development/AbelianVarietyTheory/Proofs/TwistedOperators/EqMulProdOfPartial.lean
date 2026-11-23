import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

structure CoverW {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] R₁.HK.V) : Prop where
  adj : ∀ P x, ∃ b, ∀ y, ⟪R₁.ι x, R₁.ι (B P y)⟫_ℂ = ⟪R₂.ι y, R₂.ι b⟫_ℂ
  src : ∀ Z ∈ upq p q, ∀ P y, B (fockAct1 p q r s Z P) y = R₁.HK.act Z (B P y)
  tgt : ∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure SemiW (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  bdd : ∀ φ u, ∃ c : ℝ, ∀ y : M'.sm τ, ‖⟪u, A φ y⟫_ℂ‖ ≤ c * ‖(y : M'.H τ)‖
  eqK : ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧ ∀ y, A φ' y = M.σ τ h (A φ y)
  invK : ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ φ, ∃ φ', φ'.totalDegree ≤ φ.totalDegree ∧
    ∀ y y' : M'.sm τ, (y' : M'.H τ) = M'.σ τ k y → A φ' y' = A φ y
  src : ∀ X ∈ lieAt V τ, ∀ φ y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A φ y)⟫_ℂ)
    ⟪u, A (srcOp M M' τ aT X φ) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ φ (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (tgtOp M M' τ aS Y φ) y + A φ y' = 0

structure LocW (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ) : Prop where
  kS : ∀ P y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A P y)
  kT : ∀ P u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A P y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y u, HasDerivAt (fun t : ℝ => ⟪u, M.rep τ (NormedSpace.exp (t • X)) (A P y)⟫_ℂ)
    ⟪u, A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y⟫_ℂ 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P (y y' : M'.sm τ),
    HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) y) (y' : M'.H τ) 0 →
      A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y + A P y' = 0

theorem eq_mul_prod_of_partial {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} (l : ∀ i, A i → ℂ)
    (F : (∀ i, A i) → ℂ) (h : ∀ i a, ∃ c : ℂ, ∀ x, F (Function.update a i x) = c * l i x) :
    ∃ c : ℂ, ∀ a, F a = c * ∏ i, l i (a i) := by

  have key : ∀ (a : ∀ i, A i) (i : ι) (x : A i),
      F (Function.update a i x) * l i (a i) = F a * l i x := by
    intro a i x
    obtain ⟨c, hc⟩ := h i a
    have h1 := hc (a i)
    rw [Function.update_eq_self] at h1
    rw [hc x, h1]
    ring
  by_cases hF : ∀ a, F a = 0
  · exact ⟨0, fun a => by simp [hF a]⟩
  push_neg at hF
  obtain ⟨a₀, ha₀⟩ := hF
  have hl : ∀ i, l i (a₀ i) ≠ 0 := by
    intro i hi
    obtain ⟨c, hc⟩ := h i a₀
    have h1 := hc (a₀ i)
    rw [Function.update_eq_self, hi, mul_zero] at h1
    exact ha₀ h1

  have main : ∀ s : Finset ι, ∀ a : ∀ i, A i, (∀ j, j ∉ s → a j = a₀ j) →
      F a * ∏ j ∈ s, l j (a₀ j) = F a₀ * ∏ j ∈ s, l j (a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      rw [show a = a₀ from funext fun j => ha j (by simp)]
    | @insert i s hi ih =>
      intro a ha
      have hoff : ∀ j, j ∉ s → Function.update a i (a₀ i) j = a₀ j := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          exact ha j (by simp [hji, hj])
      have e1 := ih _ hoff
      have e2 := key (Function.update a i (a₀ i)) i (a i)
      simp only [Function.update_idem, Function.update_eq_self, Function.update_self] at e2
      have hprod : ∏ j ∈ s, l j (Function.update a i (a₀ i) j) = ∏ j ∈ s, l j (a j) :=
        Finset.prod_congr rfl fun j hj => by
          have hji : j ≠ i := fun e => hi (e ▸ hj)
          rw [Function.update_of_ne hji]
      rw [hprod] at e1
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc F a * (l i (a₀ i) * ∏ j ∈ s, l j (a₀ j))
          = (F a * l i (a₀ i)) * ∏ j ∈ s, l j (a₀ j) := by ring
        _ = (F (Function.update a i (a₀ i)) * l i (a i)) * ∏ j ∈ s, l j (a₀ j) := by rw [e2]
        _ = l i (a i) * (F (Function.update a i (a₀ i)) * ∏ j ∈ s, l j (a₀ j)) := by ring
        _ = l i (a i) * (F a₀ * ∏ j ∈ s, l j (a j)) := by rw [e1]
        _ = F a₀ * (l i (a i) * ∏ j ∈ s, l j (a j)) := by ring
  have hP : ∏ j, l j (a₀ j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hl j
  refine ⟨F a₀ / ∏ j, l j (a₀ j), fun a => ?_⟩
  rw [div_mul_eq_mul_div, eq_div_iff hP]
  exact main Finset.univ a fun j hj => absurd (Finset.mem_univ j) hj

end GlobalTheory.Chain.RealLine

end
