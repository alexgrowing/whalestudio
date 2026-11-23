import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableDescendOrbitSum
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem norm_tsum_le_of_encard {I : Type} (u : I → ℂ) (S : Set I) (N : ℕ) (hS : S.encard ≤ N) (M : ℝ)
    (hM : ∀ i, ‖u i‖ ≤ M) (hM0 : 0 ≤ M) (h0 : ∀ i ∉ S, u i = 0) : ‖∑' i, u i‖ ≤ N * M := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe hS
  rw [tsum_eq_sum (s := hfin.toFinset) fun i hi => h0 i (by simpa using hi)]
  have hcard : hfin.toFinset.card ≤ N := by
    rw [hfin.encard_eq_coe_toFinset_card] at hS
    exact_mod_cast hS
  refine (norm_sum_le_of_le _ fun i _ => hM i).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM0

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbConv :
    UpperTheory.V.Cj.H.OrbConv := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f f' hf hc hf' hc'
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have hq := GlobalTheory.AutomorphicL2KernelIntegral.integrable_descend_orbitSum (Γ := Γ) hi
  obtain ⟨N, hN⟩ := (locInt G Γ μ).2 (tsupport f) hc
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hb : ∀ g, ‖GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g‖ ≤ N * M := fun g =>
    norm_tsum_le_of_encard _ _ N (hN g) M (fun _ => hM _) hM0 fun γ h => image_eq_zero_of_notMem_tsupport h
  have h : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f) := by
    refine ⟨GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum f, (memLp_two_iff_integrable_sq_norm hq.1).2 ?_⟩
    refine (hq.norm.const_mul (N * M)).mono' (hq.1.norm.pow 2) (Eventually.of_forall fun q => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  refine ⟨h, funext fun x => ?_⟩
  have hae : ∀ᵐ g ∂μ, GlobalTheory.AutomorphicL2Unitary.lift Γ h.toL2 g = GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f g := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h.coeFn_toL2] with g hg
    exact hg.trans (h.1.descend_mk g)
  have hk : Continuous fun y : G => f' (y⁻¹ * x) := by fun_prop
  have hkc : HasCompactSupport fun y : G => f' (y⁻¹ * x) :=
    hc'.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
  have hint : ∀ γ : Γ, Integrable (fun y => f (γ * y) * f' (y⁻¹ * x)) μ := fun γ =>
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hkc.mul_left
  have hfin : {γ : Γ | (γ : G) ∈ tsupport f * (tsupport fun y : G => f' (y⁻¹ * x))⁻¹}.Finite :=
    GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (IsCompact.mul hc (IsCompact.inv hkc))
  have hsum : Summable fun γ : Γ => ∫ y, ‖f (γ * y) * f' (y⁻¹ * x)‖ ∂μ := by
    refine summable_of_hasFiniteSupport (hfin.subset fun γ hγ => ?_)
    by_contra hn
    refine hγ ?_
    have : ∀ y, f (γ * y) * f' (y⁻¹ * x) = 0 := fun y => by
      by_contra hy
      exact hn ⟨_, subset_tsupport f (left_ne_zero_of_mul hy), y⁻¹,
        Set.inv_mem_inv.2 (subset_tsupport _ (right_ne_zero_of_mul hy)), by simp⟩
    simp [this]
  have e1 : ∀ γ : Γ, GlobalTheory.AutomorphicL2Unitary.conv μ f f' (γ * x) = ∫ y, f (γ * y) * f' (y⁻¹ * x) ∂μ := fun γ => by
    unfold GlobalTheory.AutomorphicL2Unitary.conv
    rw [← integral_mul_left_eq_self _ (γ : G)]
    simp [mul_assoc]
  unfold cv
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, tsum_congr e1, integral_tsum_of_summable_integral_norm hint hsum]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hy, tsum_mul_right, GlobalTheory.AutomorphicL2Unitary.orbitSum]
