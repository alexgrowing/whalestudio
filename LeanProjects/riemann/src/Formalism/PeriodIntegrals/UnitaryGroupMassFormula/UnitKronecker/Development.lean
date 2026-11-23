import Mathlib
import Formalism.PeriodIntegrals.UnitKron

namespace PI.UnitKronW

open Matrix Polynomial ComplexOrder

def StepA : Prop := ∀ (k : ℕ) (H G : Matrix (Fin k) (Fin k) ℂ), H.PosDef → Gᴴ * H * G = H →
  ∀ μ : ℂ, G.charpoly.IsRoot μ → ‖μ‖ = 1

def StepB : Prop := ∀ (E : Type) [Field E] [NumberField E] (p : E[X]), p.Monic → (∀ i, IsIntegral ℤ (p.coeff i)) →
  (∀ (φ : E →+* ℂ) (μ : ℂ), (p.map φ).IsRoot μ → ‖μ‖ = 1) →
  ∀ (φ₀ : E →+* ℂ) (μ : ℂ), (p.map φ₀).IsRoot μ → ∃ m : ℕ, 0 < m ∧ μ ^ m = 1

def StepC : Prop := ∀ (k : ℕ) (H G : Matrix (Fin k) (Fin k) ℂ), H.PosDef → Gᴴ * H * G = H →
  ∀ n : ℕ, (∀ μ ∈ G.charpoly.roots, μ ^ n = 1) → G ^ n = 1

theorem map_relation {E : Type} [Field E] (c : E →+* E) (φ : E →+* ℂ)
    (hc : ∀ x : E, φ (c x) = (starRingEnd ℂ) (φ x)) {k : ℕ} (J γ : Matrix (Fin k) (Fin k) E)
    (hγ : (γ.map c)ᵀ * J * γ = J) : (γ.map φ)ᴴ * J.map φ * γ.map φ = J.map φ := by
  have h := congrArg (fun M => M.map φ) hγ
  simp only [Matrix.map_mul] at h
  convert h using 3
  ext i j
  simp [Matrix.conjTranspose_apply, hc, Complex.star_def]

theorem unitKron_of (hA : StepA) (hB : StepB) (hC : StepC) : PI.UnitKron := by
  intro E _ _ c hc k J γ hJ hγ hint
  obtain ⟨φ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hrel : ∀ φ : E →+* ℂ, (γ.map φ)ᴴ * J.map φ * γ.map φ = J.map φ :=
    fun φ => map_relation c φ (hc φ) J γ hγ
  have hnorm : ∀ (φ : E →+* ℂ) (μ : ℂ), (γ.charpoly.map φ).IsRoot μ → ‖μ‖ = 1 := by
    intro φ μ hμ
    rw [← Matrix.charpoly_map] at hμ
    rcases hJ φ with hpos | hneg
    · exact hA k (J.map φ) (γ.map φ) hpos (hrel φ) μ hμ
    · refine hA k (-(J.map φ)) (γ.map φ) hneg ?_ μ hμ
      rw [Matrix.mul_neg, Matrix.neg_mul, hrel φ]
  have hroot : ∀ μ : ℂ, (γ.charpoly.map φ₀).IsRoot μ → ∃ m : ℕ, 0 < m ∧ μ ^ m = 1 :=
    hB E γ.charpoly (Matrix.charpoly_monic γ) hint hnorm φ₀
  classical
  let m : ℂ → ℕ := fun μ => if h : (γ.charpoly.map φ₀).IsRoot μ then (hroot μ h).choose else 1
  have hm : ∀ μ, 0 < m μ := by
    intro μ
    simp only [m]
    split_ifs with h
    · exact (hroot μ h).choose_spec.1
    · exact one_pos
  let S := (γ.map φ₀).charpoly.roots.toFinset
  obtain ⟨H, hH, hHrel⟩ : ∃ H : Matrix (Fin k) (Fin k) ℂ, H.PosDef ∧ (γ.map φ₀)ᴴ * H * γ.map φ₀ = H := by
    rcases hJ φ₀ with hpos | hneg
    · exact ⟨_, hpos, hrel φ₀⟩
    · refine ⟨_, hneg, ?_⟩
      rw [Matrix.mul_neg, Matrix.neg_mul, hrel φ₀]
  have hpow : (γ.map φ₀) ^ (∏ μ ∈ S, m μ) = 1 := by
    apply hC k H (γ.map φ₀) hH hHrel
    intro μ hμ
    have hr : (γ.charpoly.map φ₀).IsRoot μ := by
      rw [← Matrix.charpoly_map]
      exact Polynomial.isRoot_of_mem_roots hμ
    obtain ⟨t, ht⟩ : m μ ∣ ∏ ν ∈ S, m ν := Finset.dvd_prod_of_mem m (Multiset.mem_toFinset.mpr hμ)
    have hmμ : μ ^ m μ = 1 := by
      simp only [m, dif_pos hr]
      exact (hroot μ hr).choose_spec.2
    rw [ht, pow_mul, hmμ, one_pow]
  refine ⟨∏ μ ∈ S, m μ, Finset.prod_pos fun μ _ => hm μ, ?_⟩
  apply Matrix.map_injective φ₀.injective
  show (γ ^ (∏ μ ∈ S, m μ)).map φ₀ = (1 : Matrix (Fin k) (Fin k) E).map φ₀
  rw [Matrix.map_pow, hpow, Matrix.map_one _ (map_zero φ₀) (map_one φ₀)]

end PI.UnitKronW
