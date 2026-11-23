import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.LocalAtPlace

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.SBRestrProd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def levSub (d : 𝓞 F) : AddSubgroup (κ → Af F) where
  carrier := {u | ∀ i, algebraMap F (Af F) ((d : F)⁻¹) * u i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  add_mem' {u u'} hu hu' i := by
    have := add_mem (hu i) (hu' i)
    simpa [mul_add] using this
  zero_mem' i := by simp
  neg_mem' {u} hu i := by
    have := neg_mem (hu i)
    simpa [mul_neg] using this

theorem isOpen_levSub (d : 𝓞 F) : IsOpen ((levSub (κ := κ) d : AddSubgroup (κ → Af F)) : Set (κ → Af F)) := by
  have e : ((levSub (κ := κ) d : AddSubgroup (κ → Af F)) : Set (κ → Af F)) = ⋂ i, (fun z : κ → Af F =>
      algebraMap F (Af F) ((d : F)⁻¹) * z i) ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (Af F)) := by
    ext z
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [e]
  exact isOpen_iInter_of_finite fun i => (GroundTheory.Global.isOpen_integralFiniteAdeles (R := 𝓞 F) (K := F)).preimage
    (continuous_const.mul (continuous_apply i))

theorem exists_levSub_subset (V : Set (κ → Af F)) (hV : V ∈ 𝓝 (0 : κ → Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ((levSub (κ := κ) d : AddSubgroup (κ → Af F)) : Set (κ → Af F)) ⊆ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hIt⟩ := hV
  have hW : (⋂ i, t i) ∈ 𝓝 (0 : Af F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => hIt fun i _ => ?_⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (Af F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (Af F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (Af F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

def locInd (d : 𝓞 F) (a : κ → Af F) (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {y | ∀ i, algebraMap F (Fv F v) ((d : F)⁻¹) * (y i - evalV F v (a i)) ∈
    v.adicCompletionIntegers F} 1

theorem mem_levSub_iff (d : 𝓞 F) (u : κ → Af F) : u ∈ levSub (κ := κ) d ↔
    ∀ v : Pl F, ∀ i, algebraMap F (Fv F v) ((d : F)⁻¹) * evalV F v (u i) ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h v i
    have := h i v
    change evalV F v (algebraMap F (Af F) ((d : F)⁻¹) * u i) ∈ _ at this
    rw [map_mul, AlgHom.commutes] at this
    exact this
  · intro h i v
    have := h v i
    change evalV F v (algebraMap F (Af F) ((d : F)⁻¹) * u i) ∈ _
    rw [map_mul, AlgHom.commutes]
    exact this

end GlobalTheory.SBRestrProd

namespace GlobalTheory.SBRestrProd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem isClosed_integers (v : Pl F) : IsClosed (v.adicCompletionIntegers F : Set (Fv F v)) :=
  GroundTheory.Global.isClosed_adicCompletionIntegers v

theorem isCompact_integers' (v : Pl F) : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  GroundTheory.Global.isCompact_adicCompletionIntegers v

theorem coe_d_mem (d : 𝓞 F) (v : Pl F) : algebraMap F (Fv F v) (d : F) ∈ v.adicCompletionIntegers F :=
  GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v d

theorem coe_ne_zero {d : 𝓞 F} (hd : d ≠ 0) : (d : F) ≠ 0 := by
  rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]

theorem locInd_mem_SB (d : 𝓞 F) (hd : d ≠ 0) (a : κ → Af F) (v : Pl F) : locInd d a v ∈ SB (κ → Fv F v) := by
  classical
  set S : Set (κ → Fv F v) := {y | ∀ i, algebraMap F (Fv F v) ((d : F)⁻¹) * (y i - evalV F v (a i)) ∈
    v.adicCompletionIntegers F} with hS
  have hS' : S = ⋂ i, (fun y : κ → Fv F v => algebraMap F (Fv F v) ((d : F)⁻¹) * (y i - evalV F v (a i))) ⁻¹'
      (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y; simp [hS]
  have hc : ∀ i, Continuous fun y : κ → Fv F v => algebraMap F (Fv F v) ((d : F)⁻¹) * (y i - evalV F v (a i)) :=
    fun i => continuous_const.mul ((continuous_apply i).sub continuous_const)
  have hSo : IsOpen S := by
    rw [hS']; exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (hc i)
  have hSc : IsClosed S := by
    rw [hS']; exact isClosed_iInter fun i => (isClosed_integers v).preimage (hc i)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_, ?_⟩
  · by_cases hy : y ∈ S
    · filter_upwards [hSo.mem_nhds hy] with z hz
      simp only [locInd, ← hS, Set.indicator_of_mem hz, Set.indicator_of_mem hy, Pi.one_apply]
    · filter_upwards [hSc.isOpen_compl.mem_nhds hy] with z hz
      simp only [locInd, ← hS, Set.indicator_of_notMem hz, Set.indicator_of_notMem hy]
  · have hK : IsCompact ((fun w : κ → Fv F v => w + fun i => evalV F v (a i)) ''
        Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
      (isCompact_univ_pi fun _ => isCompact_integers' v).image (continuous_id.add continuous_const)
    have hsub : S ⊆ (fun w : κ → Fv F v => w + fun i => evalV F v (a i)) ''
        Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro y hy
      refine ⟨y - fun i => evalV F v (a i), fun i _ => ?_, by simp⟩
      have h1 := mul_mem (coe_d_mem d v) (hy i)
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (coe_ne_zero hd), map_one, one_mul] at h1
      simpa using h1
    exact HasCompactSupport.intro (hK.of_isClosed_subset hSc hsub) fun y hy => Set.indicator_of_notMem hy _

end GlobalTheory.SBRestrProd

namespace GlobalTheory.SBRestrProd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eventually_good (d : 𝓞 F) (a : κ → Af F) : ∀ᶠ v : Pl F in cofinite,
    algebraMap F (Fv F v) ((d : F)⁻¹) ∈ v.adicCompletionIntegers F ∧
      ∀ i, evalV F v (a i) ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) ((d : F)⁻¹)).2.and (Filter.eventually_all.2 fun i => (a i).2)

theorem locInd_eq_stdInd (d : 𝓞 F) (hd : d ≠ 0) (a : κ → Af F) (v : Pl F)
    (h1 : algebraMap F (Fv F v) ((d : F)⁻¹) ∈ v.adicCompletionIntegers F)
    (h2 : ∀ i, evalV F v (a i) ∈ v.adicCompletionIntegers F) : locInd d a v = stdInd F κ v := by
  unfold locInd stdInd
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun i => ?_
  constructor
  · intro h
    have h3 := mul_mem (coe_d_mem d v) h
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (coe_ne_zero hd), map_one, one_mul] at h3
    simpa using add_mem h3 (h2 i)
  · intro h
    exact mul_mem h1 (sub_mem h (h2 i))

theorem eventually_locInd (d : 𝓞 F) (hd : d ≠ 0) (a : κ → Af F) :
    ∀ᶠ v : Pl F in cofinite, locInd d a v = stdInd F κ v := by
  filter_upwards [eventually_good d a] with v hv
  exact locInd_eq_stdInd d hd a v hv.1 hv.2

theorem finite_mulSupport_locInd (d : 𝓞 F) (hd : d ≠ 0) (a z : κ → Af F) :
    (Function.mulSupport fun v : Pl F => locInd d a v fun i => evalV F v (z i)).Finite := by
    have hev : ∀ᶠ v : Pl F in cofinite, (algebraMap F (Fv F v) ((d : F)⁻¹) ∈ v.adicCompletionIntegers F ∧
        ∀ i, evalV F v (a i) ∈ v.adicCompletionIntegers F) ∧ ∀ i, evalV F v (z i) ∈ v.adicCompletionIntegers F :=
      (eventually_good d a).and (Filter.eventually_all.2 fun i => (z i).2)
    refine (Filter.eventually_cofinite.1 hev).subset fun v hv h => hv ?_
    show (locInd d a v fun i => evalV F v (z i)) = 1
    rw [locInd_eq_stdInd d hd a v h.1.1 h.1.2, stdInd, Set.indicator_of_mem (show (fun i => evalV F v (z i)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => h.2 i), Pi.one_apply]

open Classical in

theorem ind_eq_finprod (d : 𝓞 F) (hd : d ≠ 0) (a z : κ → Af F) :
    (if z - a ∈ levSub (κ := κ) d then (1 : ℂ) else 0) =
      ∏ᶠ v, locInd d a v fun i => evalV F v (z i) := by
  have hfin := finite_mulSupport_locInd d hd a z
  have hloc : ∀ v : Pl F, (locInd d a v fun i => evalV F v (z i)) =
      if ∀ i, algebraMap F (Fv F v) ((d : F)⁻¹) * (evalV F v (z i) - evalV F v (a i)) ∈
        v.adicCompletionIntegers F then 1 else 0 := fun v => by
    simp only [locInd, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have hmem : z - a ∈ levSub (κ := κ) d ↔ ∀ v : Pl F, ∀ i, algebraMap F (Fv F v) ((d : F)⁻¹) *
      (evalV F v (z i) - evalV F v (a i)) ∈ v.adicCompletionIntegers F := by
    rw [mem_levSub_iff]
    simp only [Pi.sub_apply, map_sub]
  by_cases h : z - a ∈ levSub (κ := κ) d
  · rw [if_pos h]
    refine (finprod_eq_one_of_forall_eq_one fun v => ?_).symm
    rw [hloc, if_pos (hmem.1 h v)]
  · rw [if_neg h]
    obtain ⟨v, hv⟩ := not_forall.1 (mt hmem.2 h)
    refine (finprod_eq_zero _ v ?_ hfin).symm
    rw [hloc, if_neg hv]

theorem exists_place : Nonempty (Pl F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

open Classical in

theorem coset_restrProd (c : ℂ) (d : 𝓞 F) (hd : d ≠ 0) (a : κ → Af F) :
    ∃ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) ∧
      ∀ z, c * (if z - a ∈ levSub (κ := κ) d then (1 : ℂ) else 0) = ∏ᶠ v, φ v fun i => evalV F v (z i) := by
  classical
  obtain ⟨v₀⟩ := exists_place (F := F)
  refine ⟨fun v => if v = v₀ then c • locInd d a v else locInd d a v, fun v => ?_, ?_, fun z => ?_⟩
  · dsimp only
    split_ifs
    · exact Submodule.smul_mem _ _ (locInd_mem_SB d hd a v)
    · exact locInd_mem_SB d hd a v
  · filter_upwards [eventually_locInd d hd a, (Set.finite_singleton v₀).eventually_cofinite_notMem] with v hv hv0
    rw [if_neg (by simpa using hv0), hv]
  · have hfin : (Function.mulSupport fun v : Pl F => locInd d a v fun i => evalV F v (z i)).Finite :=
      finite_mulSupport_locInd d hd a z
    have e : (fun v : Pl F => (if v = v₀ then c • locInd d a v else locInd d a v) fun i => evalV F v (z i)) =
        fun v => (if v = v₀ then c else 1) * locInd d a v fun i => evalV F v (z i) := by
      funext v; split_ifs <;> simp
    have hfin0 : (Function.mulSupport fun v : Pl F => if v = v₀ then c else 1).Finite := by
      refine (Set.finite_singleton v₀).subset fun v hv => ?_
      by_contra hv'
      exact hv (if_neg hv')
    rw [e, finprod_mul_distrib hfin0 hfin, ← ind_eq_finprod d hd a z,
      finprod_eq_single _ v₀ fun v hv => if_neg hv, if_pos rfl]

end GlobalTheory.SBRestrProd

namespace GlobalTheory.SBRestrProd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

open Classical in

theorem exists_sum_coset (f : (κ → Af F) → ℂ) (hf : f ∈ SB (κ → Af F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ s : Finset (κ → Af F), ∀ z,
      f z = ∑ a ∈ s, f a * (if z - a ∈ levSub (κ := κ) d then (1 : ℂ) else 0) := by
  obtain ⟨V, hV, hinv⟩ := GlobalTheory.SBTransl.exists_nhds_zero_invariant f hf.1 hf.2
  obtain ⟨d, hd, hdV⟩ := exists_levSub_subset V hV
  refine ⟨d, hd, ?_⟩
  set H := levSub (κ := κ) d with hH
  have : DiscreteTopology ((κ → Af F) ⧸ H) := QuotientAddGroup.discreteTopology (isOpen_levSub d)
  have hS : ((QuotientAddGroup.mk : (κ → Af F) → (κ → Af F) ⧸ H) '' tsupport f).Finite :=
    (hf.2.isCompact.image continuous_quotient_mk').finite_of_discrete
  have hmk : ∀ a x : κ → Af F, x - a ∈ H ↔
      (QuotientAddGroup.mk x : (κ → Af F) ⧸ H) = QuotientAddGroup.mk a := by
    intro a x
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_sub, sub_eq_neg_add]
  have hinj : Set.InjOn (fun q : (κ → Af F) ⧸ H => q.out) ↑hS.toFinset :=
    fun q _ q' _ h => by simpa using congrArg (QuotientAddGroup.mk (s := H)) h
  refine ⟨hS.toFinset.image fun q => q.out, fun x => ?_⟩
  rw [Finset.sum_image hinj]
  simp only [mul_ite, mul_one, mul_zero, hmk, QuotientAddGroup.out_eq']
  rw [Finset.sum_ite_eq]
  split_ifs with hx
  · have hq := QuotientAddGroup.out_eq' (s := H) (QuotientAddGroup.mk x)
    rw [← hmk] at hq
    have := hinv x (Quotient.out (QuotientAddGroup.mk x : (κ → Af F) ⧸ H) - x) (hdV hq)
    rw [add_sub_cancel] at this
    exact this.symm
  · exact image_eq_zero_of_notMem_tsupport fun hx' => hx ((Set.Finite.mem_toFinset hS).mpr ⟨x, hx', rfl⟩)

end GlobalTheory.SBRestrProd

namespace GlobalTheory.SBRestrProd

theorem sb_eq_sum_restrProd : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : (κ → Af F) → ℂ),
    a ∈ SB (κ → Af F) → ∃ (m : ℕ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ j v, φ j v ∈ SB (κ → Fv F v)) ∧
      (∀ j, ∀ᶠ v in cofinite, φ j v = stdInd F κ v) ∧ ∀ x, a x = ∑ j, ∏ᶠ v, φ j v fun i => evalV F v (x i) := by
  intro F _ _ κ _ f hf
  obtain ⟨d, hd, s, hs⟩ := exists_sum_coset f hf
  choose φ hφ1 hφ2 hφ3 using fun b : κ → Af F => coset_restrProd (f b) d hd b
  refine ⟨s.card, fun j => φ (s.equivFin.symm j), fun j v => hφ1 _ v, fun j => hφ2 _, fun x => ?_⟩
  rw [hs x]
  simp only [hφ3]
  rw [← Finset.sum_coe_sort s]
  exact (Equiv.sum_comp s.equivFin.symm (fun b : s => ∏ᶠ v, φ b v fun i => evalV F v (x i))).symm

end GlobalTheory.SBRestrProd

end
