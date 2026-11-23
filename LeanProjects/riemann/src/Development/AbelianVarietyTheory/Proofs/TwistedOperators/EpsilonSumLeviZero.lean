import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueSumHyperplaneZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootsWeightsPairwiseIndependentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicResidueSumZeroStatement

noncomputable section

open MeasureTheory Finset GlobalTheory.Chamber Filter Topology
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber.ConstEps

variable {k : ℕ}

theorem finrank_aP {P : Finset (SV k)} (h : IsPar P) : Module.finrank ℝ (aP P) = P.card := by
  have hli : LinearIndepOn ℝ (vec (k := k)) (P : Set (SV k)) := by
    rw [linearIndepOn_iff_notMem_span]
    intro u hu
    have := h.vec_notMem (mem_coe.1 hu)
    rwa [aP, coe_erase] at this
  have := finrank_span_eq_card (R := ℝ) hli
  rw [aP, Set.image_eq_range, this]
  simp

theorem exists_ext (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) (hQ : Q ∈ parF 𝔞 ∅) :
    ∃ F : A0 k → ℂ, Continuous F ∧ ∀ x ∈ generic k, F x = ∑ P ∈ parP 𝔞 Q, eps P Q x := by
  have hc : IsGMFam 𝔞 (fun _ _ => (1 : ℂ)) := fun P _ => ⟨contDiff_const, fun _ _ _ => rfl⟩
  have hP : ∀ P ∈ parP 𝔞 Q, IsPar P := fun P hP => (mem_parP.1 hP).1
  have hmem : ∀ P : Finset (SV k), ∀ u ∈ P \ Q, u ∈ P \ P.erase u := fun P u hu => by
    simp [(Finset.mem_sdiff.1 hu).1]
  obtain ⟨F, hF, hE⟩ := GlobalTheory.T.residue_sum_hyperplane_zero (parP 𝔞 Q) (fun P => P \ Q) (fun P => rt P)
    (fun P _ => ((√(Matrix.gram ℝ fun v : ↥(P \ Q) => rt P v).det : ℝ) : ℂ) * (∏ _v ∈ P \ Q, Complex.I)⁻¹ * 1)
    (fun P h => contDiff_const)
    (fun P h u hu => (hP P h).wt_ne_zero (Finset.erase_subset u P) (hmem P u hu))
    (fun P h u hu u' hu' ne => (GlobalTheory.T.roots_weights_pairwise_independent (hP P h) subset_rfl).1 u (Finset.mem_sdiff.1 hu).1 u'
      (Finset.mem_sdiff.1 hu').1 ne)
    (fun b hb x hx _ => GlobalTheory.T.parabolic_residue_sum_zero 𝔞 _ hc Q hQ b hb x hx)
  refine ⟨F, hF.continuous, fun x hx => ?_⟩
  rw [hE x fun P h u hu => hx P (hP P h) _ (Finset.erase_subset u P) u (hmem P u hu)]
  simp only [eps, epsOf]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  ring

theorem epsOf_smul (s : Finset (SV k)) (b : SV k → A0 k) (l : A0 k) {t : ℝ} (ht : t ≠ 0) :
    (t : ℂ) ^ s.card * epsOf s b (t • l) = epsOf s b l := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  simp only [epsOf, real_inner_smul_left]
  rw [mul_left_comm, ← prod_const, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun u _ => ?_
  push_cast
  rw [mul_left_comm Complex.I, mul_inv, ← mul_assoc, mul_inv_cancel₀ ht', one_mul]

theorem smul_mem_generic {l : A0 k} (hl : l ∈ generic k) {t : ℝ} (ht : t ≠ 0) : t • l ∈ generic k :=
  fun P hP Q hQ u hu => by
    rw [real_inner_smul_left]
    exact mul_ne_zero ht (hl P hP Q hQ u hu)

end GlobalTheory.Chamber.ConstEps

open GlobalTheory.Chamber.ConstEps in

theorem GlobalTheory.Chamber.sum_eps_eq_zero : ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)) (S : Finset (SV k)), IsLevi 𝔞 →
    S ∈ parF 𝔞 ∅ → aP S ≠ 𝔞 → ∀ l ∈ generic k, ∑ P ∈ parP 𝔞 S, eps P S l = 0 := by
  intro k 𝔞 S _ hS hne l hl
  obtain ⟨F, hF, hE⟩ := exists_ext 𝔞 S hS
  obtain ⟨hS1, hS2, -⟩ := mem_parF.1 hS
  set d := Module.finrank ℝ 𝔞 - S.card with hd
  have hd0 : d ≠ 0 := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hS2 hne)
    rw [finrank_aP hS1] at this
    omega
  have hcard : ∀ P ∈ parP 𝔞 S, (P \ S).card = d := fun P hP => by
    obtain ⟨h1, h2, h3⟩ := mem_parP.1 hP
    rw [card_sdiff_of_subset h3, ← finrank_aP h1, h2]
  have key : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ^ d * F (t • l) = ∑ P ∈ parP 𝔞 S, eps P S l := fun t ht => by
    rw [hE _ (smul_mem_generic hl ht), mul_sum]
    refine sum_congr rfl fun P hP => ?_
    rw [← hcard P hP]
    exact epsOf_smul _ _ l ht
  have hc : Continuous fun t : ℝ => (t : ℂ) ^ d * F (t • l) := by fun_prop
  have h1 : Tendsto (fun t : ℝ => (t : ℂ) ^ d * F (t • l)) (𝓝[≠] 0) (𝓝 0) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa [hd0] using this
  have h2 : Tendsto (fun t : ℝ => (t : ℂ) ^ d * F (t • l)) (𝓝[≠] 0) (𝓝 (∑ P ∈ parP 𝔞 S, eps P S l)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (key t ht).symm)
  exact tendsto_nhds_unique h2 h1

end
