import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartNormBound

open MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.SplitPrimeNormLemmas Matrix

noncomputable section

namespace WlocSk

theorem card_CI_le (k r : ℕ) : Fintype.card (NB.CI k r) ≤ r * r + r * (k + 1) + r * r := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h : Fintype.card (NB.UP r) ≤ Fintype.card (Fin r × Fin r) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

theorem dim_lt (k r : ℕ) :
    (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < N1H k r := by
  have hc := card_CI_le k r
  have h1 : 2 * (2 * Fintype.card (NB.CI k r) + r) < 4 * (2 * r + k + 1) ^ 2 := by
    have : 2 * (2 * Fintype.card (NB.CI k r) + r) ≤ 2 * (2 * (r * r + r * (k + 1) + r * r) + r) := by
      omega
    refine lt_of_le_of_lt this ?_
    nlinarith
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    push_cast; linarith
  unfold N1H
  have h1' : (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  have hp : (0 : ℝ) ≤ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

theorem nilpotent_chart_exists : NChart := by
  intro k r
  let eC := Fintype.equivFin (NB.CI k r)
  let Φ : CSp (Fintype.card (NB.CI k r)) r → Mt k r := fun t => NB.phi0 (t.1 ∘ eC) t.2
  let ψ : Mt k r → CSp (Fintype.card (NB.CI k r)) r := fun x => (NB.psiC x ∘ eC.symm, NB.psiR x)
  have hcomp : Continuous fun t : CSp (Fintype.card (NB.CI k r)) r => (t.1 ∘ eC, t.2) :=
    (continuous_pi fun i => (continuous_apply (eC i)).comp continuous_fst).prodMk continuous_snd
  have hΦc : Continuous Φ := NB.continuous_nilpotent_chart.comp hcomp
  have hψc : Continuous ψ :=
    (continuous_pi fun j => (continuous_apply (eC.symm j)).comp NB.continuous_psiC).prodMk
      NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := by
    intro t
    obtain ⟨h1, h2⟩ := NB.nilpotent_chart_right_inverse (t.1 ∘ eC) t.2
    show (NB.psiC (NB.phi0 (t.1 ∘ eC) t.2) ∘ eC.symm, NB.psiR (NB.phi0 (t.1 ∘ eC) t.2)) = t
    rw [h1, h2]
    ext j <;> simp
  have hright : ∀ x : Mt k r, Matrix.of x ∈ Nset k r → Φ (ψ x) = x := by
    intro x hx
    show NB.phi0 ((NB.psiC x ∘ eC.symm) ∘ eC) (NB.psiR x) = x
    have : (NB.psiC x ∘ eC.symm) ∘ eC = NB.psiC x := by funext i; simp
    rw [this]
    exact NB.nilpotent_chart_left_inverse hx
  have hrange : Set.range Φ = {x | Matrix.of x ∈ Nset k r} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact NB.test_vector_mem_schwartz_bruhat _ _
    · intro hx
      exact ⟨ψ x, hright x hx⟩
  refine ⟨Fintype.card (NB.CI k r), r, 2, Φ, (r : ℝ) + 2, by norm_num, dim_lt k r, by positivity,
    ?_, hrange, ?_, ?_⟩
  ·
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [this]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  ·
    intro m₀ h0
    let G : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin (Fintype.card (NB.CI k r)) → ℂ :=
      fun y j => NB.shG m₀ (y ∘ eC) (eC.symm j)
    let H : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin r → ℝ := fun y => NB.shH m₀ (y ∘ eC)
    have hyc : Continuous fun y : Fin (Fintype.card (NB.CI k r)) → ℂ => y ∘ eC :=
      continuous_pi fun i => continuous_apply (eC i)
    refine ⟨fun t => (t.1 + G t.1, t.2 + H t.1), ?_, ?_⟩
    · refine NB.shear_mp (fun j => NB.rk (eC.symm j)) G H
        (fun j => ((NB.continuous_shG m₀ (eC.symm j)).comp hyc).measurable) ?_
        ((NB.continuous_shH m₀).comp hyc).measurable
      intro j y y' hyy
      refine NB.shG_dep m₀ (eC.symm j) (y ∘ eC) (y' ∘ eC) fun i hi => ?_
      exact hyy (eC i) (by simpa using hi)
    · intro t
      obtain ⟨h1, h2⟩ := NB.lmul_coord h0 (t.1 ∘ eC) t.2
      have hmem : m₀ * NB.phi0 (t.1 ∘ eC) t.2 ∈ Nset k r := UnitaryGroupBasics.mem_n_mul h0 (NB.test_vector_mem_schwartz_bruhat _ _)
      show m₀ * NB.phi0 (t.1 ∘ eC) t.2 = NB.phi0 ((t.1 + G t.1) ∘ eC) (t.2 + H t.1)
      have e1 : (t.1 + G t.1) ∘ eC = t.1 ∘ eC + NB.shG m₀ (t.1 ∘ eC) := by
        funext i; simp [G]
      rw [e1, ← h1]
      show _ = NB.phi0 (NB.psiC (m₀ * NB.phi0 (t.1 ∘ eC) t.2)) (t.2 + NB.shH m₀ (t.1 ∘ eC))
      rw [← h2]
      exact (NB.nilpotent_chart_left_inverse hmem).symm
  ·
    intro t
    have hg := NB.nilpotent_chart_norm_bound (t.1 ∘ eC) t.2
    have hn : ‖t‖ ≤ ‖(t.1 ∘ eC, t.2)‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      refine max_le_max ?_ le_rfl
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
      have := norm_le_pi_norm (t.1 ∘ eC) (eC.symm j)
      simpa using this
    calc 1 + ‖t‖ ≤ 1 + ‖(t.1 ∘ eC, t.2)‖ := by linarith
      _ ≤ _ := hg

end WlocSk
