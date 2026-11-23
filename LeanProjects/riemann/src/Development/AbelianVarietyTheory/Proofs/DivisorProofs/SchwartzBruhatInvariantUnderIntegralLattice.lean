import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.SBTransl

theorem exists_nhds_zero_invariant {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    {β : Type} [Zero β] (g : X → β) (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ V ∈ 𝓝 (0 : X), ∀ x, ∀ u ∈ V, g (x + u) = g x := by
  have hW : ∀ x : X, {u : X | g (x + u) = g x} ∈ 𝓝 (0 : X) := fun x => by
    have h1 : IsOpen {y : X | g y = g x} := hg.isOpen_fiber _
    have h2 : Continuous fun u : X => x + u := continuous_const.add continuous_id
    exact (h2.isOpen_preimage _ h1).mem_nhds (by simp)
  choose W' hW' hW'h using fun x => exists_nhds_zero_half (hW x)
  have hU : ∀ x ∈ tsupport g, {y : X | y - x ∈ W' x} ∈ 𝓝 x := fun x _ => by
    have h2 : Continuous fun y : X => y - x := continuous_id.sub continuous_const
    exact h2.continuousAt.preimage_mem_nhds (by simpa using hW' x)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover _ hU
  set V0 : Set X := ⋂ x ∈ t, W' x
  have hV0 : V0 ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).2 fun x _ => hW' x
  have key : ∀ y ∈ tsupport g, ∀ u ∈ V0, g (y + u) = g y := fun y hy u hu => by
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hux : u ∈ W' x := Set.mem_iInter₂.1 hu x hx
    have e1 : g (x + ((y - x) + u)) = g x := hW'h x _ hyx _ hux
    have e2 : g (x + ((y - x) + 0)) = g x := hW'h x _ hyx _ (mem_of_mem_nhds (hW' x))
    rw [show x + ((y - x) + u) = y + u by abel] at e1
    rw [show x + ((y - x) + 0) = y by abel] at e2
    rw [e1, e2]
  refine ⟨V0 ∩ Neg.neg ⁻¹' V0, Filter.inter_mem hV0 (neg_mem_nhds_zero X hV0), fun x u hu => ?_⟩
  by_cases hx : x ∈ tsupport g
  · exact key x hx u hu.1
  by_cases hxu : x + u ∈ tsupport g
  · have := key (x + u) hxu (-u) hu.2
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem norm_absNorm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ < 1 := by
  have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  simpa using this

theorem exists_nat_subset_nhds {F : Type} [Field F] [NumberField F] (V : Set (FiniteAdeleRing (𝓞 F) F))
    (hV : V ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ z : FiniteAdeleRing (𝓞 F) F,
      (∀ v, ‖Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v z‖ ≤ ‖(m : Fv F v)‖) → z ∈ V := by
  classical
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v => Valued.isOpen_integer _
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : IsOpenEmbedding f := RestrictedProduct.isOpenEmbedding_structureMap hopen
  have hV' : f ⁻¹' V ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := by
    rw [← Filter.mem_map, hf.map_nhds_eq]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at hV'
  obtain ⟨I, hI, t, ht, hsub⟩ := hV'
  have hk : ∀ v, ∃ k : ℕ, ∀ y : v.adicCompletionIntegers F,
      ‖(y : v.adicCompletion F)‖ ≤ ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ k → y ∈ t v := fun v => by
    have h1 := ht v
    rw [nhds_subtype, Filter.mem_comap] at h1
    obtain ⟨s, hs, hss⟩ := h1
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_absNorm_lt_one v)
    refine ⟨k, fun y hy => hss (hball ?_)⟩
    rw [Metric.mem_ball, show ((0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) v : v.adicCompletion F) = 0 from rfl,
      dist_zero_right]
    exact lt_of_le_of_lt hy hk
  choose k hk using hk
  refine ⟨∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal ^ k v, Finset.prod_pos fun v _ =>
    pow_pos (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)) _, fun z hz => ?_⟩
  have hint : ∀ v, z v ∈ v.adicCompletionIntegers F := fun v =>
    Valued.toNormedField.norm_le_one_iff.1 ((hz v).trans (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _))
  have hz' : z = f (fun v => ⟨z v, hint v⟩) := by
    ext v; rfl
  rw [hz']
  refine hsub (fun v hv => hk v _ ?_)
  have hvI : v ∈ hI.toFinset := hI.mem_toFinset.2 hv
  refine (hz v).trans ?_
  rw [← Finset.mul_prod_erase _ _ hvI, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v _)

end GlobalTheory.SBTransl

namespace GlobalTheory.SBTransl

theorem exists_mulInt_invariant {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a → ∀ x : κ → FiniteAdeleRing (𝓞 F) F,
      g (x + fun i => (a i).2) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  obtain ⟨V, hV, hinv⟩ := exists_nhds_zero_invariant g hlc hcs
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  obtain ⟨m, hm, hmV⟩ := exists_nat_subset_nhds (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨m, hm, fun a ha x => hinv x _ (hsub fun i _ => ?_)⟩
  exact Set.mem_iInter.1 (hmV _ fun v => ha.2 v i) i

theorem transInv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) → ∃ m : ℕ, 0 < m ∧ ∀ a : κ → AF F, IsMulInt F m a →
      ∀ x : κ → FiniteAdeleRing (𝓞 F) F, g (x + fun i => (a i).2) = g x :=
  fun g hg => exists_mulInt_invariant g hg

end GlobalTheory.SBTransl
