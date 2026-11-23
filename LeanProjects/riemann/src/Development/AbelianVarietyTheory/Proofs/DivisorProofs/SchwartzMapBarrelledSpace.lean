import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter
open scoped SchwartzMap Topology Uniformity

namespace GlobalTheory
namespace SchwartzComplete

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem iteratedFDeriv_sub' (f g : 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (⇑(f - g)) x = iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n g x := by
  have hf : ContDiff ℝ n f := f.smooth n
  have hg : ContDiff ℝ n g := g.smooth n
  rw [show (⇑(f - g) : V → ℂ) = ⇑f - ⇑g from rfl]
  exact iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt

theorem cauchy_seminorm {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ a ≥ N, ∀ b ≥ N, SchwartzMap.seminorm ℝ k n (u a - u b) < ε := by
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at hu
  have h := ((schwartz_withSeminorms ℝ V ℂ).tendsto_nhds _ 0).1 hu (k, n) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h
  refine ⟨max N₁ N₂, fun a ha b hb => ?_⟩
  have := hN (b, a) (Prod.mk_le_mk.2 ⟨le_of_max_le_left hb, le_of_max_le_right ha⟩)
  simpa [schwartzSeminormFamily] using this

noncomputable def limD (u : ℕ → 𝓢(V, ℂ)) (n : ℕ) (x : V) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
  limUnder atTop fun j => iteratedFDeriv ℝ n (u j) x

theorem tendsto_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
    Tendsto (fun j => iteratedFDeriv ℝ n (u j) x) atTop (𝓝 (limD u n x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cauchy_seminorm hu 0 n hε
  refine ⟨N, fun a ha b hb => ?_⟩
  rw [dist_eq_norm, ← iteratedFDeriv_sub']
  have := SchwartzMap.le_seminorm ℝ 0 n (u a - u b) x
  simp only [pow_zero, one_mul] at this
  exact this.trans_lt (hN a ha b hb)

theorem key {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (k n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ j ≥ N, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖ ≤ ε := by
  obtain ⟨N, hN⟩ := cauchy_seminorm hu k n hε
  refine ⟨N, fun j hj x => ?_⟩
  have ht : Tendsto (fun b => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - iteratedFDeriv ℝ n (u b) x‖)
      atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u j) x - limD u n x‖)) :=
    ((tendsto_const_nhds.sub (tendsto_limD hu n x)).norm).const_mul _
  refine le_of_tendsto ht (eventually_atTop.2 ⟨N, fun b hb => ?_⟩)
  rw [← iteratedFDeriv_sub']
  exact (SchwartzMap.le_seminorm ℝ k n (u j - u b) x).trans (hN j hj b hb).le

theorem tendstoUniformly_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
    TendstoUniformly (fun j => iteratedFDeriv ℝ n (u j)) (limD u n) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := key hu 0 n (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun j hj x => ?_⟩
  have := hN j hj x
  rw [pow_zero, one_mul] at this
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem continuous_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) :
    Continuous (limD u n) :=
  (tendstoUniformly_limD hu n).continuous (Eventually.of_forall (f := atTop) fun j =>
    ((u j).smooth ⊤).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).frequently

theorem hasFDerivAt_limD {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (m : ℕ) (x : V) :
    HasFDerivAt (limD u m) ((limD u (m + 1) x).curryLeft) x := by
  refine hasFDerivAt_of_tendstoUniformly (f := fun j => iteratedFDeriv ℝ m (u j))
    (f' := fun j y => fderiv ℝ (iteratedFDeriv ℝ m (u j)) y)
    (g' := fun y => (limD u (m + 1) y).curryLeft) ?_ ?_ (fun y => tendsto_limD hu m y) x
  · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) ℂ).isometry.uniformContinuous.comp_tendstoUniformly
      (tendstoUniformly_limD hu (m + 1))
  · intro j y
    exact ((((u j).smooth ⊤).differentiable_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_lt_top (m : ℕ))) y).hasFDerivAt

theorem hasFTaylorSeries {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
    HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (limD u 0 x).curry0)
      (fun x => (fun m => limD u m x : FormalMultilinearSeries ℝ V ℂ)) where
  zero_eq _ := rfl
  fderiv m _ x := hasFDerivAt_limD hu m x
  cont m _ := continuous_limD hu m

noncomputable def limMap (u : ℕ → 𝓢(V, ℂ)) (hu : CauchySeq u) : 𝓢(V, ℂ) where
  toFun x := (limD u 0 x).curry0
  smooth' := (hasFTaylorSeries hu).contDiff
  decay' k n := by
    obtain ⟨N, hN⟩ := key hu k n one_pos
    refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
    rw [← (hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k n (u N) x
    have h3 : ‖limD u n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ + ‖iteratedFDeriv ℝ n (u N) x - limD u n x‖ := by
      have := norm_sub_le (iteratedFDeriv ℝ n (u N) x) (iteratedFDeriv ℝ n (u N) x - limD u n x)
      simpa using this
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ‖x‖ ^ k)
    change ‖x‖ ^ k * ‖limD u n x‖ ≤ _
    rw [mul_add] at h4
    linarith

theorem iteratedFDeriv_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) (n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (limMap u hu) x = limD u n x :=
  ((hasFTaylorSeries hu).eq_iteratedFDeriv (m := n) (by exact_mod_cast le_top) x).symm

theorem tendsto_limMap {u : ℕ → 𝓢(V, ℂ)} (hu : CauchySeq u) :
    Tendsto u atTop (𝓝 (limMap u hu)) := by
  rw [(schwartz_withSeminorms ℝ V ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨N, hN⟩ := key hu k n (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun j hj => ?_⟩
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (half_pos hε).le fun x => ?_
  rw [iteratedFDeriv_sub', iteratedFDeriv_limMap]
  exact hN j hj x

instance completeSpace : CompleteSpace 𝓢(V, ℂ) := by
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ⟨limMap u hu, tendsto_limMap hu⟩

end SchwartzComplete

theorem schwartzMap_barrelledSpace : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V], BarrelledSpace ℂ (SchwartzMap V ℂ) := by
  intro V _ _ _
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end GlobalTheory
