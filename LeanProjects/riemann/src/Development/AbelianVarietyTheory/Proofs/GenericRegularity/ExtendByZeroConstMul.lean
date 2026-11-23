import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsAlgebraicOfTrdegEq
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspOfIntegralAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem extendByZero_const_mul {p : ℕ} (k : ℕ) (f : Fin p → ℕ) (i : ℕ) :
    Formalism.L2.Pj.ext0 (fun s => k * f s) i = k * Formalism.L2.Pj.ext0 f i := by
  unfold Formalism.L2.Pj.ext0; split_ifs <;> simp

theorem wtA_wsmul_eq {D : D7} {j : ℕ} (k : ℕ) (w : WeightFamilies.Wt D j) : wtA (wsmul k w) = k • wtA w := by
  funext x
  simp only [wtA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : Formalism.L2.Pj.ext0 ((wsmul k w).aP t) x.2 = k * Formalism.L2.Pj.ext0 (w.aP t) x.2 := extendByZero_const_mul _ _ _
  have h2 : Formalism.L2.Pj.ext0 ((wsmul k w).aM t) x.2 = k * Formalism.L2.Pj.ext0 (w.aM t) x.2 := extendByZero_const_mul _ _ _
  rw [h1, h2]
  split_ifs <;> simp [mul_add]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem intFormSt_holds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (wL : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL), IntFormSt h j hG w := by
  intro D T h j hj hG wL N w Z k n cf b hk hcf hb
  have hw : ∀ i, ((w i : (recB h.toLawsCore).Cusp j wL) : T.R j) ∈
      cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA wL) wL.n := fun i => cutR_le T.C j wL (w i).2
  obtain ⟨g, hg, hgb⟩ := exists_cusp_of_integral_all _ _ _ _ (T.Q.Xo j) T.Q.c hG _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ)))
    (wtA wL) wL.n N (fun i => ((w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) (dom_wtA wL)
    (fun i => by rw [Formalism.L2.PjFree.cusp_ofPj]; exact hw i) Z k n cf b hk hcf hb
  rw [Formalism.L2.PjFree.cusp_ofPj, ← wtA_wsmul_eq] at hg
  have hg' : g ∈ cutR T.C j (wsmul k wL) := by
    rw [cutR_eq T.C hj]; exact hg
  exact ⟨⟨g, hg'⟩, hgb⟩

end GlobalTheory.Reg
