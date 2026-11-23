import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem Tm_row_sub (A : HSp D) (μ : D.host.E) (a : Fin A.rank) :
    (fun k => Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k) =
      Pi.single (finSumFinEquiv (Sum.inr a)) μ := by
  funext k
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases s with j | j
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl, fromRows_apply_inr, sub_self, reduceCtorEq, if_false]
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, Matrix.smul_apply, fromRows_apply_inl, fromRows_apply_inr, Matrix.neg_apply,
      Matrix.one_apply, Sum.inr.injEq, smul_eq_mul]
    by_cases h : j = a
    · subst h
      simp only [if_true]
      have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
      field_simp
      ring
    · simp [h, Ne.symm h]

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem rat_Tm_mulVec_sub (A : HSp D) (μ : D.host.E) (w : Fin (A.rank + A.rank) → AE D) (a : Fin A.rank) :
    (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) - (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inr a)) =
      incA D μ * w (finSumFinEquiv (Sum.inr a)) := by
  have hrow := Tm_row_sub A μ a
  calc _ = ∑ k, incA D ((Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k) * w k := by
        rw [mulVec, mulVec, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k =
            (Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k := congrFun hrow k
        rw [← hk, map_sub, sub_mul]
        rfl
    _ = _ := by
        rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inr a)) (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]

theorem rat_Tm_mulVec_mem_diagSub_iff (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (w : Fin (A.rank + A.rank) → AE D) :
    rat (Tm A μ) *ᵥ w ∈ diagSub (AE D) finSumFinEquiv ↔ w ∈ upperHalf D A.rank := by
  have hu : IsUnit (incA D μ) := (isUnit_iff_ne_zero.2 hμ.1).map _
  simp only [diagSub, upperHalf, LinearMap.mem_eqLocus, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply,
    Function.comp_apply, Pi.zero_apply]
  exact forall_congr' fun a => by rw [← sub_eq_zero, rat_Tm_mulVec_sub, hu.mul_right_eq_zero]

theorem exists_rat_Tm_mulVec_eq (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (v : Fin (A.rank + A.rank) → AE D)
    (hv : v ∈ diagSub (AE D) finSumFinEquiv) : ∃ w ∈ upperHalf D A.rank, rat (Tm A μ) *ᵥ w = v := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  let x : Fin A.rank → AE D := fun a => v (finSumFinEquiv (Sum.inl a))
  let w : Fin (A.rank + A.rank) → AE D := fun k => Sum.elim (rat A.gram *ᵥ x) 0 (finSumFinEquiv.symm k)
  have hw : w ∈ upperHalf D A.rank := by
    simp only [upperHalf, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply, Function.comp_apply,
      Pi.zero_apply, w, Equiv.symm_apply_apply, Sum.elim_inr, implies_true]
  have hv' : ∀ a, v (finSumFinEquiv (Sum.inl a)) = v (finSumFinEquiv (Sum.inr a)) := by
    simpa only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] using hv
  have hl : ∀ a, (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) = x a := fun a => by
    have h1 : rat (A.gram⁻¹) * rat A.gram = (1 : Mx D A.rank A.rank) := by
      rw [rat, rat, ← Matrix.map_mul, nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrFun (congrArg (· *ᵥ x) h1) a
    simp only [← mulVec_mulVec, one_mulVec] at h2
    rw [← h2, mulVec, dotProduct, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [w, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, mulVec, dotProduct, rat, map_apply, Tm, submatrix_apply, id,
      fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl]
  refine ⟨w, hw, funext fun k => ?_⟩
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  rcases s with a | a
  · exact hl a
  · have h3 := (rat_Tm_mulVec_mem_diagSub_iff A hμ w).2 hw
    simp only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] at h3
    rw [← h3 a, hl a, ← hv' a]

theorem mem_siegel_iff_chart_mem_P : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ →
    ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ siegel A ↔ κ g ∈ P D A.rank := by
  intro D A μ hμ κ hκ g
  have hT : ∀ w, rat (Tm A μ) *ᵥ (mat (κ g) *ᵥ w) = mt (dblSp A) g *ᵥ (rat (Tm A μ) *ᵥ w) := fun w => by
    rw [mulVec_mulVec, mulVec_mulVec, hκ g]
  have hP : κ g ∈ P D A.rank ↔ ∀ w, w ∈ upperHalf D A.rank ↔ mat (κ g) *ᵥ w ∈ upperHalf D A.rank := Iff.rfl
  have hS : g ∈ siegel A ↔ ∀ v, v ∈ diagSub (AE D) finSumFinEquiv ↔
      mt (dblSp A) g *ᵥ v ∈ diagSub (AE D) finSumFinEquiv := Iff.rfl
  rw [hP]
  constructor
  · intro h w
    rw [← rat_Tm_mulVec_mem_diagSub_iff A hμ, ← rat_Tm_mulVec_mem_diagSub_iff A hμ, hT]
    exact hS.1 h _
  · intro h
    refine Subgroup.mem_comap.2 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun v hv => ?_))
    obtain ⟨w, hw, rfl⟩ := exists_rat_Tm_mulVec_eq A hμ v hv
    change mt (dblSp A) g *ᵥ _ ∈ _
    rw [← hT, rat_Tm_mulVec_mem_diagSub_iff A hμ]
    exact (h w).1 hw

end GlobalTheory.StdUnn
