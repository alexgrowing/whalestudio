import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.NormSubOneLeOfHsdA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem sigLam_coe_of (hS : HlamStable) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hP : IsPsiFor ε lam T Ψ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x : Hlam ε Ψ T.w) : ((sigLam ε Ψ T.w g x : Hlam ε Ψ T.w) : L2 ε) = rreg ε g x := by
  have hx : rreg ε g x ∈ Hlam ε Ψ T.w := hS n ε lam T Ψ hP g hg x x.2
  show (((Hlam ε Ψ T.w).orthogonalProjectionOnto (rreg ε g (x : L2 ε)) : Hlam ε Ψ T.w) : L2 ε) = _
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : Hlam ε Ψ T.w))

theorem fdModel_of (hD : DegPsi) (hS : HlamStable) (hF : FormF) (hN : PsiNorm) (hM : ModelDS) : FdModel := by
  intro n ε lam T μ hl hμ
  obtain ⟨hP, hDS⟩ := hM n ε lam T μ hl hμ
  have : CompleteSpace (Hlam ε (PsiM T μ) T.w) := hDS.1
  obtain ⟨d, hd⟩ := G2.fdcGood_of_isDS hDS
  have hw : T.w ≠ 0 := G2.fdc_w_ne T
  have hj0 : uniformisationL2 ε (PsiM T μ) T.w T.w ≠ 0 := by
    intro h
    have h0 : uniformisationL2 ε (PsiM T μ) T.w (0 : T.V) = 0 := by simpa using datumEmbedding_smul hP T.w 0 (0 : T.V)
    exact hw (uniformisationL2_injective hP hw (h.trans h0.symm))
  set C : ℝ := ‖uniformisationL2 ε (PsiM T μ) T.w T.w‖ ^ 2 with hC
  have hC0 : 0 < C := by positivity
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := umat_mem_UJset ε 1
  have hdeg := hD n ε T.V (PsiM T μ) (Hlam ε (PsiM T μ) T.w) (sigLam ε (PsiM T μ) T.w)
    (fun v => ⟨uniformisationL2 ε (PsiM T μ) T.w v, datumEmbedding_mem_Hlam hP v⟩) C d (muCD ε) hC0 (fun v v' => ?_) (fun g v v' => ?_) hd
  · have hn := hN n ε lam hl T μ hμ
    rw [hdeg] at hn
    have hr : 0 < (Module.finrank ℂ T.V : ℝ) := by
      have : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
      exact_mod_cast Module.finrank_pos
    have hdim : 0 < dimVlam lam := by
      rw [dimVlam_eq_vand hl.1]
      exact div_pos (vand_pos hl.1) (Finset.prod_pos fun i _ => by positivity)
    have e := (ENNReal.ofReal_eq_ofReal_iff (by have := hd.1; positivity) (by positivity)).1 hn
    have hd' : d = dimVlam lam := by
      have h2 : (Module.finrank ℂ T.V : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp at e
      have hd0 := hd.1
      rw [div_eq_one_iff_eq hd0.ne'] at e
      exact e.symm
    rw [← hd']
    exact hd
  · have e := hF n ε lam T (PsiM T μ) hl hP hDS 1 h1 v v'
    rw [hP.2.1, (rreg_isURepOn ε).1.1] at e
    simp only [ContinuousLinearMap.one_apply] at e
    rw [Submodule.coe_inner, hC]
    push_cast at e ⊢
    exact e
  · rw [Submodule.coe_inner, sigLam_coe_of hS hP (umat_mem_UJset ε g)]
    exact hF n ε lam T (PsiM T μ) hl hP hDS _ (umat_mem_UJset ε g) v v'

end PositivityTheory.RgFd
