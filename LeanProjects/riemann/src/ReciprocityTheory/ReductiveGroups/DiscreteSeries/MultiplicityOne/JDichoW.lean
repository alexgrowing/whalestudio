import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDicho
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stDichoW (h : UnitaryGroupStructuralFacts) : StDichoW := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -, -, -, hHI, -, -, -, hClW, -⟩ := h.1
  intro k r Wp _ _ _ D X hD hX γ hγ
  obtain ⟨-, -, hgW, -, hth_mul, hth_th, -, -, hμgbar⟩ := stInvGroup h k r Wp D X hD hX γ hγ
  by_cases hWp : Subsingleton Wp
  · left
    intro x y x' y'
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  have : Nontrivial Wp := not_subsingleton_iff_nontrivial.1 hWp
  have hU : IsClosedSubgroup (UWset k r D.z) := hClW k r D.z
  have hμW := D.haarW
  have hme := MatrixSubsetMeasurability.me_val hU
  have hleft : (MatrixSubsetMeasurability.nu hU D.μW).IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμW
  have hinvI : (MatrixSubsetMeasurability.nu hU D.μW).IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμW
  have hmapnu : (MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := MatrixSubsetMeasurability.map_nu hμW
  have hνuniv : MatrixSubsetMeasurability.nu hU D.μW Set.univ = 1 := by
    have e := congrArg (fun m : Measure (Mt k r) => m Set.univ) hmapnu
    simp only [Measure.map_apply hme.measurable MeasurableSet.univ, Set.preimage_univ] at e
    rw [e, hD.mass]
  have hcpt : IsCompact {x : Mt k r | Matrix.of x ∈ UWset k r D.z} := hCW k r D.z D.z_mem D.T_pos
  have : CompactSpace (MatrixSubsetMeasurability.SG hU) := isCompact_iff_compactSpace.1 hcpt
  have hpos : (MatrixSubsetMeasurability.nu hU D.μW).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by rw [hνuniv]; exact one_ne_zero)
  have hfin : IsFiniteMeasure (MatrixSubsetMeasurability.nu hU D.μW) := ⟨by rw [hνuniv]; exact ENNReal.one_lt_top⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MatrixSubsetMeasurability.SG hU → MatrixSubsetMeasurability.SG hU, θ = fun g =>
      (MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)))⁻¹ := ⟨_, rfl⟩
  have hmθ : ∀ g, MatrixSubsetMeasurability.mat (θ g) = th k r γ (MatrixSubsetMeasurability.mat g) := by
    intro g
    simp only [hθ]
    rw [MatrixSubsetMeasurability.mat_inv, MatrixSubsetMeasurability.mat_mk]
    rfl
  have hgc : Continuous fun A : Mat k r => gbar k r γ A := by
    have h1 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A := continuous_const.matrix_mul continuous_id
    have h2 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A * embWb k r γ := h1.matrix_mul continuous_const
    have h3 : Continuous fun A : Mat k r => ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      h2.matrix_map Complex.continuous_conj
    have h4 : Continuous fun A : Mat k r =>
        embWb k r γ * ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      continuous_const.matrix_mul h3
    exact h4.matrix_mul continuous_const
  have hgbc : Continuous fun g : MatrixSubsetMeasurability.SG hU =>
      MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)) := by
    apply continuous_induced_rng.2
    exact hgc.comp MatrixSubsetMeasurability.continuous_mat
  have hθc : Continuous θ := by
    rw [hθ]
    exact hgbc.inv
  have hθmul : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply MatrixSubsetMeasurability.ext'
    rw [MatrixSubsetMeasurability.mat_mul, hmθ, hmθ, hmθ, MatrixSubsetMeasurability.mat_mul]
    exact hth_mul _ (MatrixSubsetMeasurability.mat_mem a).1 _ (MatrixSubsetMeasurability.mat_mem b).1
  have hθθ : ∀ g, θ (θ g) = g := by
    intro g
    apply MatrixSubsetMeasurability.ext'
    rw [hmθ, hmθ]
    exact hth_th _ (MatrixSubsetMeasurability.mat_mem g).1
  have hgF : Measurable fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp (hgc.comp continuous_id))
  have hθμ : (MatrixSubsetMeasurability.nu hU D.μW).map θ = MatrixSubsetMeasurability.nu hU D.μW := by
    have hval : (fun g : MatrixSubsetMeasurability.SG hU => g.1) ∘ θ =
        (invM ∘ fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) ∘ fun g : MatrixSubsetMeasurability.SG hU => g.1 := by
      funext g
      exact hmθ g
    have key : ((MatrixSubsetMeasurability.nu hU D.μW).map θ).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := by
      rw [Measure.map_map hme.measurable hθc.measurable, hval,
        ← Measure.map_map (InvGrp.measurable_invM.comp hgF) hme.measurable, hmapnu,
        ← Measure.map_map InvGrp.measurable_invM hgF, hμgbar]
      exact hHI k r _ D.μW hU hμW
    rw [← hme.comap_map ((MatrixSubsetMeasurability.nu hU D.μW).map θ), key]
    rfl
  have hπc : Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) :=
    D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat fun g => MatrixSubsetMeasurability.mat_mem g
  have hρ1 : D.π (MatrixSubsetMeasurability.mat (1 : MatrixSubsetMeasurability.SG hU)) = 1 := by
    rw [MatrixSubsetMeasurability.mat_one]
    exact D.π_rep.1
  have hρmul : ∀ a b : MatrixSubsetMeasurability.SG hU,
      D.π (MatrixSubsetMeasurability.mat (a * b)) = (D.π (MatrixSubsetMeasurability.mat a)).comp (D.π (MatrixSubsetMeasurability.mat b)) := by
    intro a b
    rw [MatrixSubsetMeasurability.mat_mul]
    exact D.π_rep.2 _ (MatrixSubsetMeasurability.mat_mem a) _ (MatrixSubsetMeasurability.mat_mem b)
  have hρn : ∀ (g : MatrixSubsetMeasurability.SG hU) (v : Wp), ‖D.π (MatrixSubsetMeasurability.mat g) v‖ = ‖v‖ :=
    fun g v => D.π_unitary _ (MatrixSubsetMeasurability.mat_mem g) v
  have hρc : ∀ v : Wp, Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) v :=
    fun v => hπc.clm_apply continuous_const
  have hmem : ∀ v w : Wp, MemLp (fun g : MatrixSubsetMeasurability.SG hU => ⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ) 2
      (MatrixSubsetMeasurability.nu hU D.μW) := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hρc v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ‖ ≤ ‖w‖ * ‖D.π (MatrixSubsetMeasurability.mat g) v‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖v‖ := by rw [hρn]
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) →
      (∀ (g : MatrixSubsetMeasurability.SG hU), ∀ v ∈ S, D.π (MatrixSubsetMeasurability.mat g) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    refine hD.irr S hS fun g hg v hv => ?_
    have e := hinv (MatrixSubsetMeasurability.mk hU g hg) v hv
    rwa [MatrixSubsetMeasurability.mat_mk] at e
  rcases schurDichotomy (MatrixSubsetMeasurability.SG hU) (MatrixSubsetMeasurability.nu hU D.μW) Wp θ (fun g => D.π (MatrixSubsetMeasurability.mat g))
      hθc hθmul hθθ hθμ hρ1 hρmul hρn hρc hmem hirr with hL | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← hmapnu, hme.integral_map]
    have e := hL x y x' y'
    simp only [hmθ] at e
    exact e
  · right
    refine ⟨C, fun g hg x y => ?_, fun g hg v => ?_⟩
    · have e := hC1 (MatrixSubsetMeasurability.mk hU g hg) x y
      simp only [hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e
    · have e := hC2 (MatrixSubsetMeasurability.mk hU g hg) v
      simp only [MatrixSubsetMeasurability.mat_inv, hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e

end ReciprocityTheory.ChartRestriction.DS.Mult1
