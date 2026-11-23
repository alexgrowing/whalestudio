import Formalism.LocalToGlobal.AlgebraicTheory.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.JetsLin
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.G (linSub JetsIn JetsIn1)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)
open Formalism.InvariantFactorPaths.G7 (at1)

namespace LinearSubstitutionJets

private theorem sum_C_scl_mul_X {K : Type} [Field K] {p : Type} [Fintype p] [DecidableEq p] (c : K)
    (x : p) :
    (∑ y, MvPowerSeries.C (scl p c x y) * MvPowerSeries.X y : MvPowerSeries p K) =
      MvPowerSeries.C c * MvPowerSeries.X x := by
  rw [Finset.sum_eq_single x]
  · simp [scl]
  · intro y _ hy
    simp [scl, Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem linSub_scl {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (c : K)
    (f : MvPowerSeries n K) :
    linSub (scl n c) f = MvPowerSeries.rescale (fun _ => c) f := by
  unfold linSub
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext i
  rw [sum_C_scl_mul_X]
  simp [MvPowerSeries.smul_eq_C_mul]

end LinearSubstitutionJets

open LinearSubstitutionJets

theorem product_scaling_jets : ProdScaleJets := by
  intro K _ _ κ n _ _ _ c r H hr hH
  classical
  have hB : ∀ a : K, a ∈ Formalism.G.unitBall K ↔ ‖a‖ ≤ 1 := fun a => Iff.rfl
  refine (Formalism.L2.Th1.G.jetsInNorm K n _).mpr ?_
  rw [linSub_scl]
  obtain ⟨hC, -, hadd, -, hmul⟩ := Formalism.L2.Th1.G.jetsRing K (Formalism.G.unitBall K) n

  have hfac : ∀ k i, JetsIn (Formalism.G.unitBall K)
      (MvPowerSeries.rescale (fun _ => c) (at1 i (H k i) : MvPowerSeries n K)) := by
    intro k i κ'
    rw [MvPowerSeries.coeff_rescale]
    unfold at1
    rw [PowerSeries.coeff_subst_single, hB]
    split_ifs with h
    · have hm : mfact κ' = (κ' i).factorial := by
        conv_lhs => rw [h]
        rw [mfact, Finsupp.prod_single_index (by simp)]
      have hp : (κ'.prod fun _ m => c ^ m) = c ^ (κ' i) := by
        conv_lhs => rw [h]
        rw [Finsupp.prod_single_index (by simp)]
      rw [hm, hp]
      calc ‖((κ' i).factorial : K) * (c ^ κ' i * PowerSeries.coeff (κ' i) (H k i))‖
          = ‖((κ' i).factorial : K) * PowerSeries.coeff (κ' i) (H k i)‖ * ‖c‖ ^ κ' i := by
            rw [norm_mul, norm_mul, norm_mul, norm_pow]
            ring
        _ ≤ 1 := hH k i (κ' i)
    · simp
  have hCr : ∀ k, JetsIn (Formalism.G.unitBall K)
      (MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K)) := by
    intro k
    have hres : MvPowerSeries.rescale (fun _ => c) (MvPowerSeries.C (r k) : MvPowerSeries n K) =
        MvPowerSeries.C (r k) := by
      ext κ'
      rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
      split_ifs with h
      · subst h
        simp
      · rw [mul_zero]
    rw [hres]
    exact hC _ ((hB _).mpr (hr k))
  unfold Formalism.L2.Th1.E.thetaProd
  rw [map_sum]
  refine Finset.sum_induction _ (JetsIn (Formalism.G.unitBall K)) (fun f g hf hg => hadd f g hf hg) ?_ ?_
  · simpa using hC 0 (Formalism.G.unitBall K).zero_mem
  · intro k _
    rw [map_mul, map_prod]
    exact hmul _ _ (hCr k)
      (Formalism.L2.Th1.G.HurwitzJetIntegrality.jetsIn_prod Formalism.L2.Th1.G.jetsRing _ _ _ fun i _ => hfac k i)

theorem linear_scaling_jets : LinScale := by
  intro K _ n m _ _ _ _ c A f
  have hS : ∀ {p q : Type} [Fintype p] [Fintype q] (B : p → q → K),
      MvPowerSeries.HasSubst
        (fun i => (∑ x, MvPowerSeries.C (B i x) * MvPowerSeries.X x : MvPowerSeries q K)) := by
    intro p q _ _ B
    exact Formalism.L2.Th1.G.hasSubst_lin B
  constructor
  · unfold linSub
    rw [MvPowerSeries.subst_comp_subst_apply (hS A) (hS (scl m c))]
    congr 1
    funext i
    show linSub (scl m c) (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) = _
    rw [← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, sum_C_scl_mul_X, map_mul]
    ring
  · unfold linSub
    rw [MvPowerSeries.subst_comp_subst_apply (hS (scl n c)) (hS A)]
    congr 1
    funext i
    rw [sum_C_scl_mul_X]
    show linSub A (MvPowerSeries.C c * MvPowerSeries.X i) = _
    rw [← Formalism.L2.Th1.G.linSubHom_apply, map_mul, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C, Formalism.L2.Th1.G.linSub_X, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_mul]
    ring

end Formalism.L2.AlgTh
