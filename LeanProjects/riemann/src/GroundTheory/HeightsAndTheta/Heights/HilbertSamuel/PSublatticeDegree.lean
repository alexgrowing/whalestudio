import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem SublatticeDegree.proof (hExt : SublatticeExtension.Statement) (hSpan : SpanningExtension.Statement)
    (hCov : CovolumeLeGram.Statement) (hGram : GramContraction.Statement) : SublatticeDegree.Statement := by
  intro E E' _ _ R R' φ φ' _ _ _ _ ψ S C hφ hφ' hψ hnorm hS hSC hC
  obtain ⟨Ψ, hΨφ, hΨn, hΨi⟩ := hExt E E' R R' φ φ' ψ hφ hφ' hψ hnorm
  set Λ := imageLattice φ with hΛdef
  set Λ' := imageLattice φ' with hΛ'def
  have hC0 : 0 < C := by linarith

  have hrk : finrank ℤ Λ' = R' := by rw [ZLattice.rank ℝ Λ', finrank_euclideanSpace_fin]
  let b' : Basis (Fin R') ℤ Λ' := Module.finBasisOfFinrankEq ℤ Λ' hrk
  let u : Fin R' → EuclideanSpace ℝ (Fin R') := fun i => (b' i : EuclideanSpace ℝ (Fin R'))
  have hcov' : ZLattice.covolume Λ' = Real.sqrt (Matrix.gram ℝ u).det :=
    GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram Λ' b'
  have hu : LinearIndependent ℝ u := by
    have he : ⇑(b'.ofZLatticeBasis ℝ Λ') = u := funext fun i => b'.ofZLatticeBasis_apply ℝ Λ' i
    rw [← he]
    exact Basis.linearIndependent _
  have hv : LinearIndependent ℝ (Ψ ∘ u) := hu.map' Ψ (LinearMap.ker_eq_bot.2 hΨi)
  have hRR : R' ≤ R := by simpa using hv.fintype_card_le_finrank

  have hspan : Submodule.span ℝ (φ '' S) = ⊤ := by
    have h1 : (Λ : Set (EuclideanSpace ℝ (Fin R))) ⊆ Submodule.span ℝ (φ '' S) := by
      intro x hx
      obtain ⟨e, rfl⟩ := AddMonoidHom.mem_range.1 hx
      clear hx
      have he : e ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top e
      induction he using AddSubgroup.closure_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | neg x _ hx => simpa using neg_mem hx
    rw [eq_top_iff, ← (IsZLattice.span_top : Submodule.span ℝ (Λ : Set (EuclideanSpace ℝ (Fin R))) = ⊤)]
    exact Submodule.span_le.2 h1

  obtain ⟨w, hwS, hind⟩ := hSpan (EuclideanSpace ℝ (Fin R)) (Fin R') (Ψ ∘ u) (φ '' S) hv hspan
  have hcard : Fintype.card (Fin R' ⊕ Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) = R := by
    simp only [Fintype.card_sum, Fintype.card_fin, finrank_euclideanSpace_fin]
    omega
  have hmem : ∀ i, Sum.elim (Ψ ∘ u) w i ∈ Λ := by
    rintro (i | j)
    · obtain ⟨e, he⟩ := AddMonoidHom.mem_range.1 (b' i).2
      refine AddMonoidHom.mem_range.2 ⟨ψ e, ?_⟩
      simp only [Sum.elim_inl, Function.comp_apply, u, ← he, hΨφ]
    · obtain ⟨s, _, hsw⟩ := hwS j
      simp only [Sum.elim_inr]
      rw [← hsw]
      exact AddMonoidHom.mem_range.2 ⟨s, rfl⟩
  have h1 := hCov R Λ _ (Sum.elim (Ψ ∘ u) w) hmem hind hcard
  have h2 := hGram (Fin R') _ (EuclideanSpace ℝ (Fin R)) Ψ u w hΨn

  have hw : ∀ j, ‖w j‖ ≤ C := fun j => by
    obtain ⟨s, hs, hsw⟩ := hwS j
    rw [← hsw]
    exact hSC s hs
  have hk : Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) ≤ R := by
    simp only [Fintype.card_fin, finrank_euclideanSpace_fin]
    omega
  have hprod : ∏ j, ‖w j‖ ^ 2 ≤ (C ^ R) ^ 2 := by
    calc ∏ j, ‖w j‖ ^ 2 ≤ ∏ _j, C ^ 2 :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hw j) 2)
      _ = (C ^ 2) ^ Fintype.card (Fin (finrank ℝ (EuclideanSpace ℝ (Fin R)) - Fintype.card (Fin R'))) := by
          rw [Finset.prod_const, Finset.card_univ]
      _ ≤ (C ^ 2) ^ R := pow_le_pow_right₀ (by nlinarith) hk
      _ = (C ^ R) ^ 2 := by ring
  have hpos' : 0 < ZLattice.covolume Λ' := ZLattice.covolume_pos Λ'
  have hpos : 0 < ZLattice.covolume Λ := ZLattice.covolume_pos Λ
  have hdu : 0 ≤ (Matrix.gram ℝ u).det := by
    rw [hcov'] at hpos'
    exact (Real.sqrt_pos.1 hpos').le
  have hmain : ZLattice.covolume Λ ≤ ZLattice.covolume Λ' * C ^ R := by
    calc ZLattice.covolume Λ ≤ Real.sqrt (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det := h1
      _ ≤ Real.sqrt ((Matrix.gram ℝ u).det * (C ^ R) ^ 2) :=
          Real.sqrt_le_sqrt (h2.trans (mul_le_mul_of_nonneg_left hprod hdu))
      _ = ZLattice.covolume Λ' * C ^ R := by
          rw [Real.sqrt_mul hdu, Real.sqrt_sq (pow_pos hC0 R).le, hcov']
  have hlog := Real.log_le_log hpos hmain
  rw [Real.log_mul hpos'.ne' (pow_pos hC0 R).ne', Real.log_pow] at hlog
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
