import ReciprocityTheory.AnalyticForms.PotentialTheory.ProdProofA
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

namespace ReciprocityTheory.AnForm.M

open MeasureTheory Filter Topology FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e e' : ℕ}

def appME (e e' : ℕ) : ((Fin e → ℂ) × (Fin e' → ℂ)) ≃ᵐ (Fin (e + e') → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin e ⊕ Fin e' => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem pp_source (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    (prodChart A B j k).source = (A.chart j).source ×ˢ (B.chart k).source := by
  simp [prodChart]

theorem pp_target (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    (prodChart A B j k).target =
      (appendCLE e e').symm ⁻¹' ((A.chart j).target ×ˢ (B.chart k).target) := by
  simp [prodChart]

theorem pp_mem_target (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)
    (y : Fin (e + e') → ℂ) :
    y ∈ (prodChart A B j k).target ↔ pr1L y ∈ (A.chart j).target ∧ pr2L y ∈ (B.chart k).target := by
  rw [pp_target]; rfl

theorem contDiffOn_comp_pr1L {f : (Fin e → ℂ) → ℝ} {s : Set (Fin e → ℂ)} {t : Set (Fin (e + e') → ℂ)}
    (hf : ContDiffOn ℝ ∞ f s) (ht : ∀ y ∈ t, pr1L y ∈ s) : ContDiffOn ℝ ∞ (fun y => f (pr1L y)) t :=
  hf.comp ((pr1L (e := e) (e' := e')).contDiff.restrict_scalars ℝ).contDiffOn ht

theorem contDiffOn_comp_pr2L {f : (Fin e' → ℂ) → ℝ} {s : Set (Fin e' → ℂ)} {t : Set (Fin (e + e') → ℂ)}
    (hf : ContDiffOn ℝ ∞ f s) (ht : ∀ y ∈ t, pr2L y ∈ s) : ContDiffOn ℝ ∞ (fun y => f (pr2L y)) t :=
  hf.comp ((pr2L (e := e) (e' := e')).contDiff.restrict_scalars ℝ).contDiffOn ht

theorem tsupport_prod_mul_subset (a : X → ℝ) (b : Y → ℝ) :
    tsupport (fun p : X × Y => a p.1 * b p.2) ⊆ tsupport a ×ˢ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).prod (isClosed_tsupport b))
  intro p hp
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
  exact ⟨subset_tsupport _ hp.1, subset_tsupport _ hp.2⟩

def prodPartition (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : ChartPartition A)
    (Q : ChartPartition B) : ChartPartition (prodAtlas A B) where
  χ i p := P.χ (finProdFinEquiv.symm i).1 p.1 * Q.χ (finProdFinEquiv.symm i).2 p.2
  smooth i i' := by
    show ContDiffOn ℝ ∞ (fun y => P.χ (finProdFinEquiv.symm i).1
        ((A.chart (finProdFinEquiv.symm i').1).symm (pr1L y)) *
      Q.χ (finProdFinEquiv.symm i).2 ((B.chart (finProdFinEquiv.symm i').2).symm (pr2L y))) _
    refine (contDiffOn_comp_pr1L (P.smooth _ _) ?_).mul (contDiffOn_comp_pr2L (Q.smooth _ _) ?_)
    · exact fun y hy => ⟨((pp_mem_target A B (finProdFinEquiv.symm i').1
        (finProdFinEquiv.symm i').2 y).1 hy.1).1, trivial⟩
    · exact fun y hy => ⟨((pp_mem_target A B (finProdFinEquiv.symm i').1
        (finProdFinEquiv.symm i').2 y).1 hy.1).2, trivial⟩
  nonneg i p := mul_nonneg (P.nonneg _ _) (Q.nonneg _ _)
  tsupport_subset i := by
    refine (tsupport_prod_mul_subset _ _).trans ?_
    show _ ⊆ (prodChart A B _ _).source
    rw [pp_source]
    exact Set.prod_mono (P.tsupport_subset _) (Q.tsupport_subset _)
  sum_eq_one p := by
    show ∑ j : Fin (A.n * B.n), P.χ (finProdFinEquiv.symm j).1 p.1 * Q.χ (finProdFinEquiv.symm j).2 p.2 = 1
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum, P.sum_eq_one, Q.sum_eq_one, one_mul]

theorem isPotential_first_projection (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : LocPot X)
    (hP : IsPotential A P) : IsPotential (prodAtlas A B) (P.pr1 (Y := Y)) :=
  isPotentialPullback A (prodAtlas A B) Prod.fst (prodAtlas_holoMap_fst A B) P hP

theorem isPotential_second_projection (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (Q : LocPot Y)
    (hQ : IsPotential B Q) : IsPotential (prodAtlas A B) (Q.pr2 (X := X)) :=
  isPotentialPullback B (prodAtlas A B) Prod.snd (prodAtlas_holoMap_snd A B) Q hQ

def onePartition {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ChartPartition (openAtlas U hU hne) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun x _ => Set.mem_univ x
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

instance openAtlas_subsingleton {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    Subsingleton (Fin (openAtlas U hU hne).n) :=
  inferInstanceAs (Subsingleton (Fin 1))

end

end ReciprocityTheory.AnForm.M
