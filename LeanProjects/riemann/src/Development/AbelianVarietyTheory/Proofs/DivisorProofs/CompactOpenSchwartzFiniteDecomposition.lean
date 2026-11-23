import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open scoped Classical

noncomputable section

namespace GlobalTheory.SchACosets

theorem exists_nhds_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {g : X → ℂ} (hg : g ∈ SB X) :
    ∃ W ∈ 𝓝 (0 : X), ∀ U : AddSubgroup X, (U : Set X) ⊆ W → ∀ x, ∀ u ∈ U, g (x + u) = g x := by
  have hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X) := fun x =>
    ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)
  choose V hV hVN using fun x => exists_nhds_zero_half (hN x)
  obtain ⟨t, -, hcov⟩ := hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ V x}) fun x _ => by
    have hc : Continuous fun y : X => y - x := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV x)
  refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV x, fun U hU => ?_⟩
  have hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    have hu' : u ∈ V x := Set.mem_iInter₂.mp (hU hu) x hxt
    have h1 : g (x + (y - x + 0)) = g x := hVN x _ hyx _ (mem_of_mem_nhds (hV x))
    have h2 : g (x + (y - x + u)) = g x := hVN x _ hyx _ hu'
    rw [add_zero, add_sub_cancel] at h1
    rw [← add_assoc, add_sub_cancel] at h2
    rw [h1, h2]
  intro y u hu
  by_cases hy : y ∈ tsupport g
  · exact hA y hy u hu
  by_cases hyu : y + u ∈ tsupport g
  · have := hA _ hyu (-u) (U.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

theorem schwartz_sum_apply {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset ι)
    (f : ι → SchwartzMap E ℂ) (x : E) : (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SchwartzMap.add_apply, ih]

theorem exists_eq_sum_pureA_cosetInd : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    ∃ W ∈ 𝓝 (0 : κ → Af F), ∀ U : AddSubgroup (κ → Af F), IsOpen (U : Set (κ → Af F)) → IsCompact (U : Set (κ → Af F)) →
      (U : Set (κ → Af F)) ⊆ W →
      ∃ (T : Finset ((κ → Af F) ⧸ U)) (G : (κ → Af F) ⧸ U → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
        (∀ (c : κ → Af F) (X : κ → mixedEmbedding.mixedSpace F),
          G (c : (κ → Af F) ⧸ U) X = Φ (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (X i)) (c i))) ∧
        Φ = ∑ q ∈ T, pureA F (G q) (GlobalTheory.CharForm.cosetInd U q) := by
  intro F _ _ κ _ Φ hΦ
  obtain ⟨n, a, v, hv⟩ := Submodule.mem_span_set'.mp hΦ
  choose f g hg hfg using fun j => (v j).2
  choose W hW hWp using fun j => exists_nhds_periodic (hg j)
  refine ⟨⋂ j, W j, Filter.iInter_mem.mpr hW, fun U hUo _ hU => ?_⟩
  haveI : DiscreteTopology ((κ → Af F) ⧸ U) := QuotientAddGroup.discreteTopology hUo
  have hout : ∀ j (x : κ → Af F), g j ((x : (κ → Af F) ⧸ U).out) = g j x := fun j x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add U x
    rw [hh]
    exact hWp j U (hU.trans (Set.iInter_subset W j)) x h h.2
  have hfin : ∀ j, (QuotientAddGroup.mk '' tsupport (g j) : Set ((κ → Af F) ⧸ U)).Finite := fun j =>
    ((hg j).2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hΦx : ∀ x : κ → AdeleRing (𝓞 F) F, Φ x = ∑ j, a j *
      (f j (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * g j (fun i => (x i).2)) := by
    intro x
    rw [← hv, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, hfg j]
    rfl
  have hG : ∀ (c : κ → Af F) (X : κ → mixedEmbedding.mixedSpace F),
      (∑ j, (g j ((c : (κ → Af F) ⧸ U).out) * a j) • f j : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) X =
        ∑ j, a j * (f j X * g j c) := by
    intro c X
    rw [schwartz_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.smul_apply, hout, smul_eq_mul]
    ring
  refine ⟨Finset.univ.biUnion fun j => (hfin j).toFinset, fun q => ∑ j, (g j q.out * a j) • f j, ?_, ?_⟩
  · intro c X
    rw [hG, hΦx]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pairA, RingEquiv.apply_symm_apply]
  · funext x
    simp only [Finset.sum_apply, pureA, GlobalTheory.CharForm.cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · rw [hG, hΦx]
    · rw [hΦx]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h0 : g j (fun i => (x i).2) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hxs
        exact hx (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, (hfin j).mem_toFinset.mpr ⟨_, hxs, rfl⟩⟩)
      rw [h0, mul_zero, mul_zero]

end GlobalTheory.SchACosets
