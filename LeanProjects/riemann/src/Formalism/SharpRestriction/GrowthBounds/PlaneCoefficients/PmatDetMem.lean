import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem det_mem_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => h _ _) _

theorem X_mem_supp {R σ : Type*} [CommRing R] (s : Set σ) (i : σ) (hi : i ∈ s) :
    (X i : MvPolynomial σ R) ∈ supported R s := by
  rw [supported_eq_adjoin_X]
  exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hi)

theorem pmat_det_mem (R : Type) [CommRing R] {n' r k : ℕ} (hrk : r ≤ k) (A : Fin r → Fin n') (P : Fin r → ℕ)
    (hA : ∀ l, Even (A l).val) :
    (pmat R hrk A P).det ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
  apply det_mem_sub
  intro l i
  unfold pmat
  rw [Matrix.of_apply]
  exact Subalgebra.pow_mem _ (X_mem_supp {v : TV n' k | v.2.val < r ∧ Even v.1.val} (A l, Fin.castLE hrk i)
    (show (Fin.castLE hrk i).val < r ∧ Even (A l).val from ⟨i.isLt, hA l⟩)) _

theorem restSP : RestSP := by
  intro p n' r k _ R _ F hrk c' Q L₁ N₁ hV hn hr ga hga v hv
  have hfr : ∀ (j : ℤ) (l : Fin r), Even (posOf n' (F.fr j l.val)).val := fun j l =>
    (posOf_even hn _).2 (hV.2.2.2.2.1 j l.val l.isLt).2
  have hAr : ∀ (s : ℤ) (l : Fin r), Even (posOf n' (Arow F s l.val)).val := fun s l =>
    (posOf_even hn _).2 (window_holds_even_tops n' r F L₁ N₁ hV hn hr s l.val l.isLt).1
  have hmem : SPR R p F hrk c' Q ∈ supported R {v : TV n' k | v.2.val < r ∧ Even v.1.val} := by
    unfold SPR
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _)
      (Subalgebra.prod_mem _ fun j _ => ?_)) (Subalgebra.prod_mem _ fun s _ => ?_)
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hfr j)) _
    · exact Subalgebra.pow_mem _ (pmat_det_mem R hrk _ _ (hAr _)) _
  have hvars : v ∈ (SPR R p F hrk c' Q).vars :=
    (mem_vars v).2 ⟨ga, hga, Finsupp.mem_support_iff.2 hv⟩
  exact (mem_supported.1 hmem) (Finset.mem_coe.2 hvars)

end Formalism.MainNotions.PairMembershipBlocks
