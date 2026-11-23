import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairsA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

variable {k r : ℕ}

theorem gN_map_conj (M : Mat k r) : gN (M.map (starRingEnd ℂ)) = gN M := by
  simp only [gN, Matrix.map_apply, Complex.normSq_conj]

theorem gN_le_gbar {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det) (y : Mat k r) :
    gN y ≤ (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 * gN (gbar k r γ y) := by
  obtain ⟨y', hy'⟩ : ∃ y', y' = gbar k r γ y := ⟨_, rfl⟩
  have h1 : gN y = gN (gbar k r γ y') := by rw [hy', InvGrp.gbar_gbar hE]
  rw [h1, ← hy']
  unfold gbar
  set E := embWb k r γ
  have hE0 := gN_nonneg E
  have hEi0 := gN_nonneg E⁻¹
  calc gN (E * (E⁻¹ * y' * E).map (starRingEnd ℂ) * E⁻¹)
      ≤ gN E * gN ((E⁻¹ * y' * E).map (starRingEnd ℂ)) * gN E⁻¹ :=
        (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hEi0)
    _ = gN E * gN (E⁻¹ * y' * E) * gN E⁻¹ := by rw [gN_map_conj]
    _ ≤ gN E * (gN E⁻¹ * gN y' * gN E) * gN E⁻¹ := by
        gcongr
        exact (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hE0)
    _ = (gN E * gN E⁻¹) ^ 2 * gN y' := by ring

theorem rpow_bound {A B K a : ℝ} (hA : 0 < A) (hK : 0 < K) (ha : 0 ≤ a) (h : A ≤ K * B) :
    B ^ (-a) ≤ K ^ a * A ^ (-a) := by
  have hB : A / K ≤ B := by rw [div_le_iff₀ hK, mul_comm]; exact h
  have hAK : 0 < A / K := div_pos hA hK
  calc B ^ (-a) ≤ (A / K) ^ (-a) := Real.rpow_le_rpow_of_nonpos hAK hB (by linarith)
    _ = K ^ a * A ^ (-a) := by
      rw [Real.div_rpow hA.le hK.le, Real.rpow_neg hK.le, div_eq_mul_inv, inv_inv, mul_comm]

theorem inner_sig_sig (X : SigData k r) {h : Mat k r} (hh : h ∈ GV k r) (a b : X.Hs) :
    ⟪X.σ h a, X.σ h b⟫_ℂ = ⟪a, b⟫_ℂ := (⟨(X.σ h).toLinearMap, X.rep.2.1 h hh⟩ : X.Hs →ₗᵢ[ℂ] X.Hs).inner_map_map a b

theorem inner_sig_left (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) {h : Mat k r} (hh : h ∈ GV k r)
    (a b : X.Hs) : ⟪X.σ h a, b⟫_ℂ = ⟪a, X.σ h⁻¹ b⟫_ℂ := by
  have hi : h⁻¹ ∈ GV k r := hG.inv_mem h hh
  have hb : X.σ h (X.σ h⁻¹ b) = b := by
    have e := X.rep.1.2 h hh h⁻¹ hi
    rw [Matrix.mul_nonsing_inv _ (hG.unit h hh), X.rep.1.1] at e
    have e2 := congrArg (fun T : X.Hs →L[ℂ] X.Hs => T b) e
    simpa using e2.symm
  conv_lhs => rw [← hb]
  exact inner_sig_sig X hh a _

theorem exists_inner_ne (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) (v : X.Hs) (hv : v ≠ 0) :
    ∃ g ∈ GV k r, ⟪v, X.σ g X.w⟫_ℂ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let S : Submodule ℂ X.Hs :=
    { carrier := {u | ∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0}
      add_mem' := by
        intro a b ha hb g hg
        rw [map_add, inner_add_right, ha g hg, hb g hg, add_zero]
      zero_mem' := by
        intro g hg
        rw [map_zero, inner_zero_right]
      smul_mem' := by
        intro c a ha g hg
        rw [map_smul, inner_smul_right, ha g hg, mul_zero] }
  have hSc : IsClosed (S : Set X.Hs) := by
    have e : (S : Set X.Hs) = ⋂ g ∈ GV k r, (fun u => ⟪v, X.σ g u⟫_ℂ) ⁻¹' {0} := by
      ext u
      show (∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0) ↔ _
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact isClosed_biInter fun g _ => isClosed_singleton.preimage (continuous_const.inner (X.σ g).continuous)
  have hSi : ∀ g ∈ GV k r, ∀ u ∈ S, X.σ g u ∈ S := by
    intro g hg u hu g' hg'
    have e := X.rep.1.2 g' hg' g hg
    have e2 : X.σ g' (X.σ g u) = X.σ (g' * g) u := by rw [e]; rfl
    show ⟪v, X.σ g' (X.σ g u)⟫_ℂ = 0
    rw [e2]
    exact hu _ (hG.mul_mem g' hg' g hg)
  have hw : X.w ∈ S := fun g hg => hcon g hg
  rcases X.irr S hSc hSi with h | h
  · have h0 : X.w = 0 := by
      rw [h] at hw
      exact (Submodule.mem_bot ℂ).mp hw
    have h1 := X.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  · have hv' : v ∈ S := by rw [h]; exact Submodule.mem_top
    have h0 := hv' 1 hG.one_mem
    rw [X.rep.1.1, ContinuousLinearMap.one_apply, inner_self_eq_zero] at h0
    exact hv h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds
