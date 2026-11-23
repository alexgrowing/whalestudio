import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Topology Filter

theorem pureA_fixed_fin :
    ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
      ∃ M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m ∈ M, ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  intro F _ _ ψ hψ κ _ g hg
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  let χ := GlobalTheory.HeisSchA.finChar ψ
  have hL : IsOpen {a | χ a = 1} := (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).isOpen_fiber 1
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2

  obtain ⟨V0, hV0⟩ : ∃ V0 : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ u ∈ V0, ∀ v ∈ V0, χ (c * (u ⬝ᵥ v)) = 1 := by
    have hcont : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        c * (p.1 ⬝ᵥ p.2) :=
      continuous_const.mul (continuous_fst.dotProduct continuous_snd)
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        χ (c * (p.1 ⬝ᵥ p.2)) = 1 := by
      rw [← nhds_prod_eq]
      refine hcont.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
      simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff (r := fun a b => χ (c * (a ⬝ᵥ b)) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun u hu v hv => hss u (hV hu) v (hV hv)⟩

  have hloc : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∃ V : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ a ∈ V, ∀ u ∈ V, g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1 := by
    intro y
    have c1 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        y + p.1 + p.2 := (continuous_const.add continuous_fst).add continuous_snd
    have c2 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (y + p.1) ⬝ᵥ p.2 := (continuous_const.add continuous_fst).dotProduct continuous_snd
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        g (y + p.1 + p.2) = g y ∧ χ ((y + p.1) ⬝ᵥ p.2) = 1 := by
      rw [← nhds_prod_eq]
      refine Filter.Eventually.and (c1.continuousAt.preimage_mem_nhds ((hg.1.isOpen_fiber (g y)).mem_nhds ?_))
        (c2.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_))
      · simp
      · simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff
      (r := fun a u => g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun a ha u hu => hss a (hV ha) u (hV hu)⟩
  choose V hV using hloc
  obtain ⟨t, -, htK⟩ := (hg.2 : IsCompact (tsupport g)).elim_nhds_subcover
    (fun y => {z | z - y ∈ (V y : Set (κ → FiniteAdeleRing (𝓞 F) F))}) (fun y _ => by
      refine (continuous_sub_right y).continuousAt.preimage_mem_nhds ?_
      rw [sub_self]
      exact (V y).isOpen.mem_nhds (V y).zero_mem)
  let M0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (V0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) ⊓ ⨅ y ∈ t, (V y : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
  have hM0 : ∀ u ∈ M0, u ∈ V0 ∧ ∀ y ∈ t, u ∈ V y := fun u hu => by
    simp only [M0, AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hu
    exact ⟨hu.1, hu.2⟩
  have hM0open : IsOpen (M0 : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    refine M0.isOpen_of_mem_nhds (g := 0) ?_
    refine Filter.mem_of_superset (Filter.inter_mem (V0.isOpen.mem_nhds V0.zero_mem)
      ((Filter.biInter_finset_mem t).2 fun y _ => (V y).isOpen.mem_nhds (V y).zero_mem)) ?_
    intro u hu
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hu
    simp only [M0, SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
    exact ⟨hu.1, hu.2⟩
  have hcov : ∀ y ∈ tsupport g, ∀ u ∈ M0, g (y + u) = g y ∧ ∀ v ∈ M0, χ (y ⬝ᵥ v) = 1 := by
    intro y hy u hu
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ t, y - z ∈ V z := by simpa using htK hy
    have e : z + (y - z) = y := by abel
    have h1 := hV z (y - z) hyz u ((hM0 u hu).2 z hz)
    have h2 := hV z (y - z) hyz 0 (V z).zero_mem
    rw [e] at h1 h2
    rw [add_zero] at h2
    refine ⟨h1.1.trans h2.1.symm, fun v hv => ?_⟩
    have h3 := hV z (y - z) hyz v ((hM0 v hv).2 z hz)
    rw [e] at h3
    exact h3.2
  have hinv : ∀ u ∈ M0, ∀ y, g (y + u) = g y := by
    intro u hu y
    by_cases hy : y ∈ tsupport g
    · exact (hcov y hy u hu).1
    by_cases hy' : y + u ∈ tsupport g
    · have := (hcov (y + u) hy' (-u) (M0.neg_mem hu)).1
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']
  refine ⟨M0.prod M0, by rw [AddSubgroup.coe_prod]; exact hM0open.prod hM0open, ?_⟩
  rintro ⟨u, v⟩ hm f
  rw [AddSubgroup.mem_prod] at hm
  obtain ⟨hu, hv⟩ := hm
  funext x
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA, finE2]
  have harg : x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v) =
      ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) := by
    have hp1 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p1 (finE F w i) = 0 := fun _ _ => rfl
    have hp2 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p2 (finE F w i) = w i := fun _ _ => rfl
    refine Prod.ext ?_ ?_
    · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = 0
      simp only [map_add, map_mul, dotProduct, map_sum, hp1, mul_zero, Finset.sum_const_zero, add_zero]
    · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = _
      simp only [map_add, map_mul, dotProduct, map_sum, hp2]
      rfl
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + finE F u) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    rw [show ((x + finE F u) i).1 = (x i).1 from add_zero (x i).1]
  have hgx : (fun i => ((x + finE F u) i).2) = (fun i => (x i).2) + u := by
    funext i
    rfl
  rw [harg, hf, hgx, hinv u hu]
  by_cases h0 : g (fun i => (x i).2) = 0
  · rw [h0]
    ring
  · have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport g h0
    have e1 := (hcov _ hy u hu).2 v hv
    have e2 := hV0 u (hM0 u hu).1 v (hM0 v hv).1
    have : ψ ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1 := by
      change χ ((fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1
      rw [AddChar.map_add_eq_mul, e1, e2, one_mul]
    rw [this, one_mul]

end GlobalTheory.WeilAdm
