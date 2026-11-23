import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDicho

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiM_inv' {k r : ℕ} (u : Formalism.REAL.UJ (epsG k r)) : psiM k r u⁻¹ = (psiM k r u)⁻¹ := by
  exact (Matrix.inv_eq_right_inv (by rw [← psiM_mul, mul_inv_cancel, psiM_one])).symm

theorem stDichoG (h : UnitaryGroupStructuralFacts) : StDichoG := by
  intro k r Wp _ _ _ D X hD hSq γ hγ
  obtain ⟨hgbG, -, -, -, hanti', hinv', hμG, -, -⟩ := stInvGroup h k r Wp D X hD hSq γ hγ
  have hG := D.haarG
  haveI := nuG_left hG
  haveI := nuG_inv hG
  haveI := nuG_openPos hG
  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun e => by have hw := X.w_norm; simp [e] at hw⟩⟩
  have inj := (isClosedEmbedding_psiM k r).injective

  have hex : ∀ u : Formalism.REAL.UJ (epsG k r), ∃ u', psiM k r u' = gbar k r γ (psiM k r u) := by
    intro u
    have hm : gbar k r γ (psiM k r u) ∈ Set.range (psiM k r) := by
      rw [range_psiM]
      exact hgbG _ (psiM_mem u)
    exact hm
  choose G hGs using hex
  let θ : Formalism.REAL.UJ (epsG k r) → Formalism.REAL.UJ (epsG k r) := fun u => (G u)⁻¹
  have hθ : ∀ u, psiM k r (θ u) = th k r γ (psiM k r u) := by
    intro u
    simp only [θ, th, psiM_inv', hGs]
  have hanti : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply inj
    rw [hθ, psiM_mul, psiM_mul, hθ, hθ]
    exact hanti' _ (psiM_mem a) _ (psiM_mem b)
  have hinv : ∀ u, θ (θ u) = u := by
    intro u
    apply inj
    rw [hθ, hθ]
    exact hinv' _ (psiM_mem u)
  have hgbar : Continuous (gbar k r γ) := by
    unfold gbar
    exact ((continuous_const.matrix_mul ((((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_map Complex.continuous_conj))).matrix_mul continuous_const)
  have hGc : Continuous G := by
    rw [(isClosedEmbedding_psiM k r).toIsEmbedding.continuous_iff]
    have e : psiM k r ∘ G = gbar k r γ ∘ psiM k r := funext hGs
    rw [e]
    exact hgbar.comp (continuous_psiM k r)
  have hθc : Continuous θ := continuous_inv.comp hGc
  have hE := measurableEmbedding_psiG k r
  let T : Mt k r → Mt k r := fun x => fun i j => th k r γ (Matrix.of x) i j
  have hT : AEMeasurable T D.μG := by
    by_contra hne
    rw [Measure.map_of_not_aemeasurable hne] at hμG
    exact D.haarG.ne_zero hμG.symm
  have hcomp : psiG k r ∘ θ = T ∘ psiG k r := by
    funext u
    show Matrix.of.symm (psiM k r (θ u)) = fun i j => th k r γ (Matrix.of (psiG k r u)) i j
    rw [of_psiG, hθ]
    rfl
  have key : ((nuG D.μG).map θ).map (psiG k r) = (nuG D.μG).map (psiG k r) := by
    rw [Measure.map_map hE.measurable hθc.measurable, hcomp,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [map_nuG hG]; exact hT) hE.measurable.aemeasurable,
      map_nuG hG]
    exact hμG
  have hmap : (nuG D.μG).map θ = nuG D.μG := by
    calc (nuG D.μG).map θ = (((nuG D.μG).map θ).map (psiG k r)).comap (psiG k r) := (hE.comap_map _).symm
      _ = ((nuG D.μG).map (psiG k r)).comap (psiG k r) := by rw [key]
      _ = nuG D.μG := hE.comap_map _
  have hSR := sqRep_psiG hG X.rep (fun v w => hSq v w)
  rcases schurDichotomy (Formalism.REAL.UJ (epsG k r)) (nuG D.μG) X.Hs θ (fun u => X.σ (psiM k r u)) hθc hanti hinv
      hmap hSR.one hSR.mul hSR.iso hSR.cont hSR.sq (irr_psiG X.irr) with h0 | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← map_nuG hG, hE.integral_map]
    simp only [of_psiG, ← hθ]
    exact h0 x y x' y'
  · right
    refine ⟨C, ?_, ?_⟩
    · intro g hg x y
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ]
      exact hC1 u x y
    · intro g hg v
      obtain ⟨u, rfl⟩ : g ∈ Set.range (psiM k r) := by rw [range_psiM]; exact hg
      rw [← hθ, ← psiM_inv']
      exact hC2 u v

end ReciprocityTheory.ChartRestriction.DS.Mult1
