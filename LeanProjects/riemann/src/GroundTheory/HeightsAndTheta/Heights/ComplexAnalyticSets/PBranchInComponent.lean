import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Metric Filter Topology Set

noncomputable section

namespace BranchInComponent

theorem differentiable_eval {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem exists_open_prod_ne_zero {k : ℕ} {U : Set (Fin k → ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hne : U.Nonempty) {ι : Type*} (s : Finset ι) (f : ι → (Fin k → ℂ) → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) U) (hnz : ∀ i ∈ s, ¬ EqOn (f i) 0 U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ x ∈ V, ∏ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨U, subset_rfl, hU, hne, fun x _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨V, hVU, hVo, ⟨z, hz⟩, hV⟩ :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hnz i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨w, hwV, hw⟩ : ∃ w ∈ V, f a w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hnz a (Finset.mem_insert_self a s)
        (hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc (hVU hz) ?_)
      filter_upwards [hVo.mem_nhds hz] with x hx using hcon x hx
    refine ⟨V ∩ f a ⁻¹' {0}ᶜ, inter_subset_left.trans hVU,
      (hfa.continuousOn.mono hVU).isOpen_inter_preimage hVo isOpen_compl_singleton, ⟨w, hwV, hw⟩, ?_⟩
    rintro x ⟨hxV, hx⟩
    rw [Finset.prod_insert ha]
    exact mul_ne_zero hx (hV x hxV)

theorem proof : BranchInComponent.Statement := by
  classical
  intro n I k q c
  by_contra hcon
  push Not at hcon
  set B : Set (Fin k → ℂ) := ball 0 c.radius with hB
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball (0 : Fin k → ℂ) c.radius).isPreconnected
  have hBne : B.Nonempty := ⟨0, mem_ball_self c.radius_pos⟩
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

  have hch : ∀ J : I.minimalPrimes, ∃ g ∈ (J : Ideal (MvPolynomial (Fin n) ℂ)),
      ¬ EqOn (fun τ => eval (c.toFun τ) g) 0 B := by
    intro J
    have hJ := hcon J J.2
    simp only [Set.MapsTo, not_forall, exists_prop] at hJ
    obtain ⟨τ, hτB, hτZ⟩ := hJ
    simp only [zeroSet, mem_ofPred_eq, not_forall] at hτZ
    obtain ⟨g, hg, hgτ⟩ := hτZ
    exact ⟨g, hg, fun h => hgτ (h hτB)⟩
  choose g hgJ hgnz using hch
  let _ : Fintype I.minimalPrimes := hfin.fintype
  have han : ∀ J : I.minimalPrimes, AnalyticOnNhd ℂ (fun τ => eval (c.toFun τ) (g J)) B := fun J =>
    IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hBo
      ((differentiable_eval (g J)).comp_differentiableOn c.differentiableOn)
  obtain ⟨V, hVB, -, ⟨x, hx⟩, hV⟩ := exists_open_prod_ne_zero hBo hBc hBne Finset.univ
    (fun J τ => eval (c.toFun τ) (g J)) (fun J _ => han J) (fun J _ => hgnz J)

  set G : MvPolynomial (Fin n) ℂ := ∏ J : I.minimalPrimes, g J with hG
  have hGrad : G ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro J hJ
    rw [hG, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ ⟨J, hJ⟩)]
    exact Ideal.mul_mem_right _ _ (hgJ ⟨J, hJ⟩)
  obtain ⟨N, hN⟩ := hGrad
  have h0 := c.mapsTo (hVB hx) _ hN
  rw [map_pow, hG, map_prod] at h0
  exact hV x hx (pow_eq_zero_iff'.1 h0).1

end BranchInComponent

end

end GroundTheory.Heights₂.Heights
