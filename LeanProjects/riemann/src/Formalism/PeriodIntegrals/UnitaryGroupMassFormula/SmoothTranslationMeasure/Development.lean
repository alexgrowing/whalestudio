import Formalism.PeriodIntegrals.PhMeasCore

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)

def StepRed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin n) (Fin n) ℂ),
    IsUnit P → Pᴴ * Jm ε * P = Hm →
    (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) →
    IsUnit Hm ∧ MulOnUH Hm σ

def StepExp : Prop :=
  ∀ (n : ℕ) (Hm X : Matrix (Fin n) (Fin n) ℂ), IsUnit Hm → InLie Hm X →
    ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm

def StepSub : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → w ∈ smoothVecs Hm σ →
    (∀ g ∈ UH Hm, σ g w ∈ smoothVecs Hm σ) ∧
    ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, v - v' ∈ smoothVecs Hm σ

section Deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def StepExpDeriv : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0

end Deriv

def StepWord : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → (∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm) →
    w ∈ smoothVecs Hm σ →
    ∀ ws : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ ws, InLie Hm X) →
      ContinuousOn (fun g => dsigW σ ws (σ g w)) (UH Hm) ∧
      ∀ g ∈ UH Hm, ∀ g₀ ∈ UH Hm,
        dsigW σ ws (σ g w - σ g₀ w) = dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)

theorem isClosed_UH {n : ℕ} (Hm : Matrix (Fin n) (Fin n) ℂ) : IsClosed (UH Hm) := isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
  continuous_id) continuous_const

theorem continuousOn_B {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Wp : Type} [NormedAddCommGroup Wp]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {B : H → Wp} {w : H}
    (hS : StepSub) (hW : StepWord) (hmul : MulOnUH Hm σ)
    (hexp : ∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm)
    (hadd : ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v + v') = B v + B v')
    (hB : IsCWCont Hm σ B) (hw : w ∈ smoothVecs Hm σ) :
    ContinuousOn (fun g => B (σ g w)) (UH Hm) := by
  obtain ⟨C, Ws, hWs, hBd⟩ := hB
  have hS' := hS n Hm H σ w hmul hw
  have hsub : ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v - v') = B v - B v' := by
    intro v hv v' hv'
    have h := hadd (v - v') (hS'.2 v hv v' hv') v' hv'
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  intro g₀ hg₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto
      (fun g => C * (Ws.map fun ws => ‖dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)‖).sum)
      (nhdsWithin g₀ (UH Hm)) (nhds 0) := by
    have h := Filter.Tendsto.const_mul C (tendsto_list_sum (f := fun ws g => ‖dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)‖)
      (a := fun ws => ‖dsigW σ ws (σ g₀ w) - dsigW σ ws (σ g₀ w)‖) Ws fun ws hws =>
      Filter.Tendsto.norm (Filter.Tendsto.sub
        ((hW n Hm H σ w hmul hexp hw ws (hWs ws hws)).1 g₀ hg₀) tendsto_const_nhds))
    convert h using 2
    simp
  refine squeeze_zero' (Filter.Eventually.of_forall fun g => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with g hg
  have h1 := hS'.1 g hg
  have h0 := hS'.1 g₀ hg₀
  rw [← hsub _ h1 _ h0]
  refine (hBd _ (hS'.2 _ h1 _ h0)).trans (le_of_eq ?_)
  congr 2
  refine List.map_congr_left fun ws hws => ?_
  rw [(hW n Hm H σ w hmul hexp hw ws (hWs ws hws)).2 g hg g₀ hg₀]

theorem phMeasCore_of (hR : StepRed) (hE : StepExp) (hS : StepSub) (hW : StepWord) : PI.PhMeasCore := by
  intro n ε Hm H _ _ Wp _ _ σ B w ⟨P, hP, hPH, hσ, _⟩ hadd _ hB hw
  obtain ⟨hu, hmul⟩ := hR n ε Hm H σ P hP hPH hσ
  have hexp : ∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm :=
    fun X hX t => hE n Hm X hu hX t
  have hc : ContinuousOn (fun g => B (σ g w)) (UH Hm) :=
    continuousOn_B hS hW hmul hexp hadd hB hw
  have hof : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
  have hcl : IsClosed {x : Fin n → Fin n → ℂ | Matrix.of x ∈ UH Hm} :=
    (isClosed_UH Hm).preimage hof
  classical
  rw [← Set.piecewise_eq_indicator]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hcl.measurableSet
  exact (hc.comp hof.continuousOn fun x hx => hx).norm

end PI.PhMeasCore.UnitaryGroupMassFormula

end
