import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

open Filter Topology

theorem tendsto_sum_placeIdem {F : Type} [Field F] [NumberField F]
    (α : HeightOneSpectrum (𝓞 F) → GlobalTheoryTheory.GenusMassVolumes.Af F) (h1 : ∀ v, evalV F v (α v) = 1)
    (h0 : ∀ v v', v' ≠ v → evalV F v' (α v) = 0) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∑ v ∈ s, α v) atTop (𝓝 1) := by
  classical
  have hv : ∀ (s : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)),
      evalV F w (1 - ∑ v ∈ s, α v) = if w ∈ s then 0 else 1 := by
    intro s w
    rw [map_sub, map_one, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw (fun v _ hvw => h0 v w (Ne.symm hvw)), h1, sub_self]
    · rw [Finset.sum_eq_zero (fun v hvs => h0 v w (by rintro rfl; exact hw hvs)), sub_zero]

  let y : Finset (HeightOneSpectrum (𝓞 F)) → (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
    fun s w => if w ∈ s then 0 else 1
  have hy : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with s hs
    have hws : w ∈ s := Finset.singleton_subset_iff.mp hs
    simp [y, hws]
  let g : ((w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F) → GlobalTheoryTheory.GenusMassVolumes.Af F :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) Filter.cofinite
  have hg : Continuous g := RestrictedProduct.isEmbedding_structureMap.continuous
  have hgy : ∀ s, g (y s) = 1 - ∑ v ∈ s, α v := by
    intro s
    refine FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => ?_)
    have e1 : (g (y s)) w = ((y s w : w.adicCompletionIntegers F) : w.adicCompletion F) := rfl
    have e2 : (1 - ∑ v ∈ s, α v) w = evalV F w (1 - ∑ v ∈ s, α v) := rfl
    rw [e1, e2, hv]
    by_cases hw : w ∈ s <;> simp [y, hw]
  have hg0 : g 0 = 0 := FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => rfl)
  have hlim : Tendsto (fun s => 1 - ∑ v ∈ s, α v) atTop (𝓝 (0 : GlobalTheoryTheory.GenusMassVolumes.Af F)) := by
    have h := (hg.tendsto 0).comp hy
    rw [hg0] at h
    exact h.congr (fun s => hgy s)
  simpa using (tendsto_const_nhds (x := (1 : GlobalTheoryTheory.GenusMassVolumes.Af F))).sub hlim

theorem tendsto_truncation : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  intro D ε hε a ha
  choose α hαε hα1 hα0 using hε
  have hsum : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ∑ v ∈ s, ε v = pairA D.host.F 0 (∑ v ∈ s, α v) := by
    intro s
    simp only [hαε]
    exact (map_sum (AddMonoidHom.inr (InfiniteAdeleRing D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) α s).symm
  have hpair : Continuous (pairA D.host.F 0) := by
    show Continuous fun y : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => ((0 : InfiniteAdeleRing D.host.F), y)
    exact continuous_const.prodMk continuous_id
  have hlimF : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => ∑ v ∈ s, ε v) atTop
      (𝓝 (pairA D.host.F 0 1)) := by
    simp_rw [hsum]
    exact (hpair.tendsto 1).comp (tendsto_sum_placeIdem α hα1 hα0)

  have hidem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * a = a := by
    have hsplit : pairA D.host.F 0 1 = 1 - pairA D.host.F 1 0 := by
      rw [eq_sub_iff_add_eq]
      show ((0 + 1, 1 + 0) : InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F) = 1
      rw [zero_add, add_zero]
      rfl
    have hr : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) = GlobalTheory.SplitScalar.realIdem D := by
      rw [GlobalTheory.SplitScalar.realIdem, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsplit, map_sub, map_one, hr, sub_mul, one_mul, GlobalTheory.SplitScalar.realIdem_mul_of_fin ha, sub_zero]
  have hT := hlimF.smul_const a
  rw [Algebra.smul_def, hidem] at hT
  exact hT.congr (fun s => Algebra.smul_def _ _)

end GlobalTheory.VecInv

end
