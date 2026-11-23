import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqFinsetSumPureTensorCosetIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.SchADecomp

open Topology Filter

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def intA : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v : Pl F, a v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem evalV_eq (v : Pl F) (a : FiniteAdeleRing (𝓞 F) F) : evalV F v a = a v := rfl

theorem intA_eq_range : ((intA F : AddSubgroup _) : Set (FiniteAdeleRing (𝓞 F) F)) =
    Set.range (RestrictedProduct.structureMap (fun v : Pl F => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
  ext a
  constructor
  · intro h
    exact ⟨fun v => ⟨a v, h v⟩, rfl⟩
  · rintro ⟨x, rfl⟩ v
    exact (x v).2

theorem isOpen_intA : IsOpen ((intA F : AddSubgroup _) : Set (FiniteAdeleRing (𝓞 F) F)) := by
  rw [intA_eq_range]
  exact (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _)).isOpen_range

theorem isCompact_intA : IsCompact ((intA F : AddSubgroup _) : Set (FiniteAdeleRing (𝓞 F) F)) := by
  haveI : CompactSpace (∀ v : Pl F, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :=
    @Pi.compactSpace _ _ _ (fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [intA_eq_range]
  have hc := (RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : Pl F => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_integer _)).continuous
  exact isCompact_range hc

variable (F) in

def intP (κ : Type) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) := AddSubgroup.pi Set.univ fun _ => intA F

theorem isOpen_intP (κ : Type) [Fintype κ] : IsOpen ((intP F κ : AddSubgroup _) : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  rw [intP, AddSubgroup.coe_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intA

theorem isCompact_intP (κ : Type) : IsCompact ((intP F κ : AddSubgroup _) : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  rw [intP, AddSubgroup.coe_pi]
  exact isCompact_univ_pi fun _ => isCompact_intA

theorem exists_open_invariant {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [NonarchimedeanAddGroup X] (g : X → ℂ) (hg : g ∈ SB X) :
    ∃ M : AddSubgroup X, IsOpen (M : Set X) ∧ ∀ u ∈ M, ∀ y, g (y + u) = g y := by
  have hloc : ∀ y : X, ∃ V : OpenAddSubgroup X, ∀ u ∈ V, g (y + u) = g y := by
    intro y
    have h0 : {u | g (y + u) = g y} ∈ 𝓝 (0 : X) := by
      have hc : Continuous fun u : X => y + u := continuous_const.add continuous_id
      exact hc.continuousAt.preimage_mem_nhds (x := 0)
        ((hg.1.isOpen_fiber (g y)).mem_nhds (show g (y + 0) = g y by rw [add_zero]))
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    exact ⟨V, fun u hu => hV hu⟩
  choose V hV using hloc
  obtain ⟨t, -, htK⟩ := (hg.2 : IsCompact (tsupport g)).elim_nhds_subcover
    (fun y => {z | z - y ∈ (V y : Set X)}) (fun y _ => by
      refine (continuous_sub_right y).continuousAt.preimage_mem_nhds ?_
      rw [sub_self]
      exact (V y).isOpen.mem_nhds (V y).zero_mem)
  let M0 : AddSubgroup X := ⨅ y ∈ t, (V y : AddSubgroup X)
  have hM0 : ∀ u ∈ M0, ∀ y ∈ t, u ∈ V y := fun u hu => by
    simp only [M0, AddSubgroup.mem_iInf] at hu; exact hu
  have hM0open : IsOpen (M0 : Set X) := by
    refine M0.isOpen_of_mem_nhds (g := 0) ?_
    refine Filter.mem_of_superset ((Filter.biInter_finset_mem t).2 fun y _ => (V y).isOpen.mem_nhds (V y).zero_mem) ?_
    intro u hu
    simp only [Set.mem_iInter] at hu
    simp only [M0, SetLike.mem_coe, AddSubgroup.mem_iInf]
    exact hu
  have hcov : ∀ y ∈ tsupport g, ∀ u ∈ M0, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ t, y - z ∈ V z := by simpa using htK hy
    have h1 := hV z (y - z + u) ((V z).add_mem hyz ((hM0 u hu) z hz))
    have h2 := hV z (y - z) hyz
    rw [show z + (y - z + u) = y + u by abel] at h1
    rw [show z + (y - z) = y by abel] at h2
    rw [h1, h2]
  refine ⟨M0, hM0open, fun u hu y => ?_⟩
  by_cases hy : y ∈ tsupport g
  · exact hcov y hy u hu
  by_cases hy' : y + u ∈ tsupport g
  · have := hcov (y + u) hy' (-u) (M0.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

theorem exists_nsmul_mem (κ : Type) [Fintype κ] (M : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
    (hM : IsOpen (M : Set (κ → FiniteAdeleRing (𝓞 F) F))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ a ∈ intP F κ, N • a ∈ M := by
  haveI : CompactSpace (intP F κ) := isCompact_iff_compactSpace.1 (isCompact_intP κ)
  have ho : IsOpen ((M.addSubgroupOf (intP F κ)) : Set (intP F κ)) := hM.preimage continuous_subtype_val
  haveI : Finite (intP F κ ⧸ M.addSubgroupOf (intP F κ)) := AddSubgroup.quotient_finite_of_isOpen _ ho
  refine ⟨(M.addSubgroupOf (intP F κ)).index, AddSubgroup.index_ne_zero_of_finite, fun a ha => ?_⟩
  have := AddSubgroup.nsmul_index_mem (M.addSubgroupOf (intP F κ)) (⟨a, ha⟩ : intP F κ)
  rw [AddSubgroup.mem_addSubgroupOf] at this
  simpa using this

end GlobalTheory.SchADecomp

namespace GlobalTheory.SchADecomp

open Topology Filter

variable {F : Type} [Field F] [NumberField F]

def locInd {κ : Type} (c : FiniteAdeleRing (𝓞 F) F) (r : κ → FiniteAdeleRing (𝓞 F) F) (v : Pl F) :
    (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, c v * (x i - r i v) ∈ v.adicCompletionIntegers F} 1

theorem natCast_mul_apply {N : ℕ} {c : FiniteAdeleRing (𝓞 F) F} (hNc : (N : FiniteAdeleRing (𝓞 F) F) * c = 1)
    (v : Pl F) : (N : Fv F v) * c v = 1 := by
  have := congrArg (evalV F v) hNc
  rw [map_mul, map_natCast, map_one] at this
  exact this

theorem locInd_std {κ : Type} [Fintype κ] {N : ℕ} {c : FiniteAdeleRing (𝓞 F) F}
    (hNc : (N : FiniteAdeleRing (𝓞 F) F) * c = 1) (r : κ → FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ v in Filter.cofinite, locInd c r v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
  have hc : ∀ᶠ v in Filter.cofinite, c v ∈ v.adicCompletionIntegers F := c.2
  have hr : ∀ᶠ v in Filter.cofinite, ∀ i, r i v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (r i).2
  filter_upwards [hc, hr] with v hcv hrv
  have hNv := natCast_mul_apply hNc v
  unfold locInd
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    have e : x i = (N : Fv F v) * (c v * (x i - r i v)) + r i v := by
      linear_combination (-(x i - r i v)) * hNv
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ N) (h i)) (hrv i)
  · intro h i
    exact mul_mem hcv (sub_mem (h i) (hrv i))

theorem locInd_mem_SB {κ : Type} [Fintype κ] {N : ℕ} {c : FiniteAdeleRing (𝓞 F) F}
    (hNc : (N : FiniteAdeleRing (𝓞 F) F) * c = 1) (r : κ → FiniteAdeleRing (𝓞 F) F) (v : Pl F) :
    locInd c r v ∈ SB (κ → Fv F v) := by
  have hc0 : c v ≠ 0 := right_ne_zero_of_mul_eq_one (natCast_mul_apply hNc v)
  let h : (κ → Fv F v) ≃ₜ (κ → Fv F v) :=
    (Homeomorph.subRight (fun i => r i v)).trans (Homeomorph.smulOfNeZero (c v) hc0)
  have e : locInd c r v = Set.indicator {x : κ → Fv F v | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 ∘ h := by
    funext x
    simp only [locInd, Function.comp_apply, Set.indicator_apply, Set.mem_setOf_eq, h, Homeomorph.trans_apply,
      Homeomorph.subRight_apply, Homeomorph.smulOfNeZero_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.one_apply]
  have hs := GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) v
  rw [e]
  exact ⟨hs.1.comp_continuous h.continuous, hs.2.comp_homeomorph h⟩

theorem ind_eq_finprod {κ : Type} [Fintype κ] {N : ℕ} {c : FiniteAdeleRing (𝓞 F) F}
    (hNc : (N : FiniteAdeleRing (𝓞 F) F) * c = 1) (r : κ → FiniteAdeleRing (𝓞 F) F) (x : κ → AF F) :
    Set.indicator {y | c • (y - r) ∈ intP F κ} (fun _ => (1 : ℂ)) (fun i => (x i).2) =
      ∏ᶠ v, locInd c r v (fun i => evFin F v (x i)) := by
  by_cases hy : (fun i => (x i).2) ∈ {y | c • (y - r) ∈ intP F κ}
  · rw [Set.indicator_of_mem hy]
    symm
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    have hy' : c • ((fun i => (x i).2) - r) ∈ intP F κ := hy
    have hm : (fun i => evFin F v (x i)) ∈
        {x' : κ → Fv F v | ∀ i, c v * (x' i - r i v) ∈ v.adicCompletionIntegers F} := by
      intro i
      exact (AddSubgroup.mem_pi _).1 hy' i (Set.mem_univ i) v
    unfold locInd
    rw [Set.indicator_of_mem hm]
    rfl
  · rw [Set.indicator_of_notMem hy]
    have hex : ∃ v, (fun i => evFin F v (x i)) ∉
        {x' : κ → Fv F v | ∀ i, c v * (x' i - r i v) ∈ v.adicCompletionIntegers F} := by
      by_contra hcon
      push_neg at hcon
      refine hy ((AddSubgroup.mem_pi _).2 fun i _ => ?_)
      intro v
      exact hcon v i
    obtain ⟨v, hv⟩ := hex
    symm
    refine finprod_eq_zero _ v ?_ (GlobalTheory.PureFactor.mulSupport_finite _ (locInd_std hNc r) x)
    unfold locInd
    rw [Set.indicator_of_notMem hv]

theorem pureA_eq_sum (κ : Type) [Fintype κ] (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (N : ℕ) (c : FiniteAdeleRing (𝓞 F) F) (R : Finset (κ → FiniteAdeleRing (𝓞 F) F)),
      (N : FiniteAdeleRing (𝓞 F) F) * c = 1 ∧
      pureA F f g = ∑ r ∈ R, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g r • f) (fun v => locInd c r v) := by
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  obtain ⟨M, hMo, hMinv⟩ := exists_open_invariant g hg
  obtain ⟨N, hN, hNM⟩ := exists_nsmul_mem κ M hMo
  obtain ⟨c, hcdef⟩ : ∃ c : FiniteAdeleRing (𝓞 F) F, c = algebraMap F _ ((N : F)⁻¹) := ⟨_, rfl⟩
  have hNc : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [hcdef, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one]
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (intP F κ).comap (DistribMulAction.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c)
  have hmemU : ∀ y, y ∈ U ↔ c • y ∈ intP F κ := fun y => Iff.rfl
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun y => c • y
      invFun := fun y => (N : FiniteAdeleRing (𝓞 F) F) • y
      left_inv := fun y => by simp only [smul_smul, hNc, one_smul]
      right_inv := fun y => by simp only [smul_smul, mul_comm c, hNc, one_smul]
      continuous_toFun := continuous_const_smul c
      continuous_invFun := continuous_const_smul _ }
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) = (fun y => c • y) ⁻¹' (intP F κ : Set _) :=
    Set.ext fun y => Iff.rfl
  have hh : (⇑h : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F)) = fun y => c • y := rfl
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    rw [hUset]
    exact (isOpen_intP κ).preimage (continuous_const_smul c)
  have hUc : IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    rw [hUset, ← hh]
    exact h.isCompact_preimage.2 (isCompact_intP κ)
  have hUM : ∀ u ∈ U, u ∈ M := by
    intro u hu
    have := hNM _ ((hmemU u).1 hu)
    rwa [← Nat.cast_smul_eq_nsmul (FiniteAdeleRing (𝓞 F) F), smul_smul, hNc, one_smul] at this
  have hinv : ∀ x, ∀ u ∈ U, pureA F f g (x + GlobalTheory.WeilAdm.finE F u) = pureA F f g x := by
    intro x u hu
    have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + GlobalTheory.WeilAdm.finE F u) i).1) =
        fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
      funext i
      rw [show ((x + GlobalTheory.WeilAdm.finE F u) i).1 = (x i).1 from add_zero (x i).1]
    have h2 : (fun i => ((x + GlobalTheory.WeilAdm.finE F u) i).2) = (fun i => (x i).2) + u := by
      funext i
      rfl
    simp only [pureA]
    rw [h1, h2, hMinv u (hUM u hu)]
  have hsupp : ∀ x, (fun i => (x i).2) ∉ tsupport g → pureA F f g x = 0 := by
    intro x hx
    simp only [pureA]
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  obtain ⟨R, -, hdec⟩ := GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator F κ U (tsupport g) hUo hUc hg.2
  refine ⟨N, c, R, hNc, ?_⟩
  rw [hdec (pureA F f g) hinv hsupp]
  refine Finset.sum_congr rfl fun r _ => ?_
  funext x
  have e1 : GlobalTheory.WeilAdm.slice F (pureA F f g) r (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) =
      g r * f (fun i => evI F (x i)) := by
    simp only [GlobalTheory.WeilAdm.slice, pureA, RingEquiv.apply_symm_apply]
    rw [mul_comm]
    rfl
  have e2 := ind_eq_finprod hNc r x
  show GlobalTheory.WeilAdm.slice F (pureA F f g) r (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) *
      Set.indicator {y | c • (y - r) ∈ intP F κ} (fun _ => (1 : ℂ)) (fun i => (x i).2) =
    (g r • f) (fun i => evI F (x i)) * ∏ᶠ v, locInd c r v (fun i => evFin F v (x i))
  rw [e1, e2, SchwartzMap.smul_apply, smul_eq_mul]

end GlobalTheory.SchADecomp

theorem GlobalTheory.SchADecomp.exists_sum_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Ψ : (κ → AF F) → ℂ), Ψ ∈ schA F κ →
    ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ),
      (∀ i v, φ i v ∈ SB (κ → Fv F v)) ∧
      (∀ i v, v ∉ T → φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) ∧
      Ψ = ∑ i, pure (f i) (φ i) := by
  intro F _ _ κ _ Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨N, c, R, hNc, hsum⟩ := GlobalTheory.SchADecomp.pureA_eq_sum κ f g hg
    have hfin : ∀ r : κ → FiniteAdeleRing (𝓞 F) F, {v : Pl F | ¬ GlobalTheory.SchADecomp.locInd c r v =
        Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1}.Finite :=
      fun r => Filter.eventually_cofinite.1 (GlobalTheory.SchADecomp.locInd_std hNc r)
    let e := R.equivFin
    refine ⟨R.biUnion fun r => (hfin r).toFinset, R.card, fun i => g (e.symm i) • f,
      fun i v => GlobalTheory.SchADecomp.locInd c (e.symm i).1 v, fun i v => GlobalTheory.SchADecomp.locInd_mem_SB hNc _ v,
      fun i v hv => ?_, ?_⟩
    · by_contra hne
      exact hv (Finset.mem_biUnion.2 ⟨(e.symm i).1, (e.symm i).2, (hfin _).mem_toFinset.2 hne⟩)
    · rw [hsum, ← Finset.sum_coe_sort R]
      exact Fintype.sum_equiv e _ _ (fun r => by simp)
  | zero => exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨T1, m1, f1, φ1, hs1, ht1, he1⟩ := h1
    obtain ⟨T2, m2, f2, φ2, hs2, ht2, he2⟩ := h2
    refine ⟨T1 ∪ T2, m1 + m2, Fin.append f1 f2, Fin.append φ1 φ2, ?_, ?_, ?_⟩
    · intro i v
      induction i using Fin.addCases with
      | left j => rw [Fin.append_left]; exact hs1 j v
      | right j => rw [Fin.append_right]; exact hs2 j v
    · intro i v hv
      induction i using Fin.addCases with
      | left j => rw [Fin.append_left]; exact ht1 j v (fun h => hv (Finset.mem_union_left _ h))
      | right j => rw [Fin.append_right]; exact ht2 j v (fun h => hv (Finset.mem_union_right _ h))
    · rw [Fin.sum_univ_add, he1, he2]
      simp only [Fin.append_left, Fin.append_right]
  | smul a Φ _ h =>
    obtain ⟨T, m, f, φ, hs, ht, he⟩ := h
    refine ⟨T, m, fun i => a • f i, φ, hs, ht, ?_⟩
    rw [he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul]
    ring
