import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocalGlobalIndex
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLatticeOfLocalisations
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct IsDedekindDomain Submodule
open GroundTheory.Heights₂.Heights

noncomputable section

namespace LocalGlobalIndex

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_approx_finset (T : Finset (HeightOneSpectrum (𝓞 K))) (N : 𝓞 K) (hN : N ≠ 0)
    (r : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hr : ∀ v ∈ T, r v ∈ v.adicCompletionIntegers K) :
    ∃ a : 𝓞 K, ∀ v ∈ T, ∃ o ∈ v.adicCompletionIntegers K,
      algebraMap K (v.adicCompletion K) (a : K) - r v =
        algebraMap K (v.adicCompletion K) (N : K) * o := by
  classical
  have h : ∀ v ∈ T, ∃ c : 𝓞 K, (∃ o ∈ v.adicCompletionIntegers K,
        algebraMap K (v.adicCompletion K) (c : K) - r v =
          algebraMap K (v.adicCompletion K) (N : K) * o) ∧
      ∀ u ∈ T, u ≠ v → ∃ o ∈ u.adicCompletionIntegers K,
        algebraMap K (u.adicCompletion K) (c : K) = algebraMap K (u.adicCompletion K) (N : K) * o :=
    fun v hv => Theta.Ex1GL.exists_approx v T N hN (hr v hv)
  choose! c hc hc' using h
  refine ⟨∑ w ∈ T, c w, fun v hv => ?_⟩
  obtain ⟨o, ho, hov⟩ := hc v hv
  have hw : ∀ w ∈ T.erase v, ∃ o ∈ v.adicCompletionIntegers K,
      algebraMap K (v.adicCompletion K) (c w : K) = algebraMap K (v.adicCompletion K) (N : K) * o :=
    fun w hw => hc' w (Finset.mem_of_mem_erase hw) v hv (Finset.ne_of_mem_erase hw).symm
  choose! o' ho' hov' using hw
  refine ⟨o + ∑ w ∈ T.erase v, o' w, add_mem ho (sum_mem fun w hw => ho' w hw), ?_⟩
  have e : ((∑ w ∈ T, c w : 𝓞 K) : K) = (c v : K) + ∑ w ∈ T.erase v, (c w : K) := by
    rw [← Finset.add_sum_erase T c hv]
    push_cast
    rfl
  rw [e, map_add, map_sum, Finset.sum_congr rfl hov', ← Finset.mul_sum, mul_add, ← hov]
  ring

theorem exists_mem_near (L : Submodule (𝓞 K) V) (hL : L.FG) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (N : 𝓞 K) (hN : N ≠ 0) (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K ⊗[K] V)
    (hy : ∀ v ∈ T, y v ∈ localLattice v L) :
    ∃ x ∈ L, ∀ v ∈ T, ∃ w ∈ localLattice v L,
      toLocal v x - y v = algebraMap K (v.adicCompletion K) (N : K) • w := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  have hLv : ∀ v : HeightOneSpectrum (𝓞 K), localLattice v L =
      span (v.adicCompletionIntegers K) (Set.range fun i => toLocal v (g i)) := fun v => by
    rw [← hg, LatticeOfLocalisations.localLattice_span, ← Set.range_comp]
    rfl
  have hc : ∀ v ∈ T, ∃ cc : Fin n → v.adicCompletionIntegers K,
      ∑ i, cc i • toLocal v (g i) = y v := by
    intro v hv
    have h := hy v hv
    rw [hLv v] at h
    exact (mem_span_range_iff_exists_fun _).mp h
  choose! cc hcc using hc
  have ha : ∀ i, ∃ a : 𝓞 K, ∀ v ∈ T, ∃ o ∈ v.adicCompletionIntegers K,
      algebraMap K (v.adicCompletion K) (a : K) - (cc v i : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) (N : K) * o :=
    fun i => exists_approx_finset T N hN (fun v => (cc v i : v.adicCompletion K))
      fun v _ => (cc v i).2
  choose a hav using ha
  refine ⟨∑ i, a i • g i, sum_mem fun i _ => L.smul_mem _ (hg ▸ subset_span ⟨i, rfl⟩),
    fun v hv => ?_⟩
  choose o ho hov using fun i => hav i v hv
  refine ⟨∑ i, (⟨o i, ho i⟩ : v.adicCompletionIntegers K) • toLocal v (g i), ?_, ?_⟩
  · rw [hLv v]
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  · rw [← hcc v hv, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LatticeOfLocalisations.toLocal_smul', ← algebraMap_smul (v.adicCompletion K) (cc v i),
      ← algebraMap_smul (v.adicCompletion K) (⟨o i, ho i⟩ : v.adicCompletionIntegers K),
      smul_smul]
    convert congrArg (· • toLocal v (g i)) (hov i) using 1
    · exact (sub_smul (algebraMap K (v.adicCompletion K) (a i : K)) (cc v i : v.adicCompletion K)
        (toLocal v (g i))).symm
    · rfl

theorem mem_of_forall_toLocal_mem (M : FullLattice K V) {x : V}
    (hx : ∀ v, toLocal v x ∈ localLattice v M.carrier) : x ∈ M.carrier := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M.fg
  have hgK : span K (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← M.span_eq, span_le, ← hg]
    exact fun x hx => span_le_restrictScalars (𝓞 K) K (Set.range g) hx
  have : Module.Finite K V :=
    ⟨⟨Finset.univ.image g, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgK]⟩⟩
  let e := Module.finBasis K V
  obtain ⟨c, hc, hcF⟩ := LatticeOfLocalisations.exists_smul_mem_span_basis e g
  let F₀ : FullLattice K V := ⟨span (𝓞 K) (Set.range e), fg_span (Set.finite_range e),
    by rw [Submodule.span_span_of_tower, e.span_eq]⟩
  obtain ⟨d, hd, hdF⟩ := exists_smulSub_le M F₀
  set b := d * c with hb_def
  have hb : b ≠ 0 := mul_ne_zero hd hc
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  set T := (finite_mem_asIdeal hb).toFinset with hT
  obtain ⟨x₁, hx₁, hnear⟩ :=
    exists_mem_near M.carrier M.fg T b hb (fun v => toLocal v x) fun v _ => hx v
  set z : V := (b : K)⁻¹ • (x - x₁) with hz
  have hzv : ∀ v, toLocal v z ∈ localLattice v M.carrier := by
    intro v
    have hz' : toLocal v z =
        (algebraMap K (v.adicCompletion K) (b : K))⁻¹ • (toLocal v x - toLocal v x₁) := by
      rw [hz, map_smul, map_sub, ← algebraMap_smul (v.adicCompletion K) (b : K)⁻¹, map_inv₀]
    by_cases hv : v ∈ T
    · obtain ⟨w, hw, hxw⟩ := hnear v hv
      rw [hz', ← neg_sub, hxw, smul_neg, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).mpr hbK),
        one_smul]
      exact neg_mem hw
    · have hbv : b ∉ v.asIdeal := by simpa [hT] using hv
      rw [hz']
      exact LatticeOfLocalisations.smul_mem_of_mem_integers v _
        (Theta.Ex1GL.inv_mem_of_notMem v hbv) (sub_mem (hx v) (subset_span ⟨x₁, hx₁, rfl⟩))
  have hcz : c • z ∈ span (𝓞 K) (Set.range e) := by
    refine LatticeOfLocalisations.mem_span_of_forall_toLocal_mem e fun v => ?_
    rw [LatticeOfLocalisations.toLocal_smul']
    exact LatticeOfLocalisations.smul_localLattice_mem v c
      (fun m hm => hcF m (by rw [hg]; exact hm)) (hzv v)
  have hbz : b • z ∈ M.carrier := by
    rw [hb_def, mul_smul]
    exact hdF (mem_smulSub_of_mem d hcz)
  have hxz : b • z = x - x₁ := by
    rw [← algebraMap_smul K b z, hz, smul_smul, ← RingOfIntegers.coe_eq_algebraMap,
      mul_inv_cancel₀ hbK, one_smul]
  have h := add_mem hbz hx₁
  rwa [hxz, sub_add_cancel] at h

end LocalGlobalIndex

open LocalGlobalIndex in

theorem LocalGlobalIndex.proof : LocalGlobalIndex.Statement := by
  intro K _ _ V _ _ _ _ M₁ M₂ h21
  classical
  obtain ⟨b, hb, hbM⟩ := exists_smulSub_le M₂ M₁
  have hbM' : ∀ m ∈ M₁.carrier, b • m ∈ M₂.carrier := fun m hm => hbM (mem_smulSub_of_mem b hm)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  set S := (finite_mem_asIdeal hb).toFinset with hS
  have hout : ∀ v, v ∉ S → localLattice v M₁.carrier ≤ localLattice v M₂.carrier := by
    intro v hv y hy
    have hbv : b ∉ v.asIdeal := by simpa [hS] using hv
    have e : y = (algebraMap K (v.adicCompletion K) (b : K))⁻¹ •
        (algebraMap K (v.adicCompletion K) (b : K) • y) := by
      rw [smul_smul, inv_mul_cancel₀ ((map_ne_zero _).mpr hbK), one_smul]
    rw [e]
    exact LatticeOfLocalisations.smul_mem_of_mem_integers v _
      (Theta.Ex1GL.inv_mem_of_notMem v hbv) (LatticeOfLocalisations.smul_localLattice_mem v b hbM' hy)
  let A := fun v : HeightOneSpectrum (𝓞 K) => (localLattice v M₁.carrier).toAddSubgroup
  let B := fun v : HeightOneSpectrum (𝓞 K) => (localLattice v M₂.carrier).toAddSubgroup
  let ι : ∀ v, M₁.carrier →+ A v := fun v =>
    { toFun := fun m => ⟨toLocal v (m : V), subset_span ⟨m, m.2, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun m m' => by ext; simp }
  let Φ : M₁.carrier →+ ∀ v : S, A v.1 ⧸ (B v.1).addSubgroupOf (A v.1) :=
    AddMonoidHom.pi fun v => (QuotientAddGroup.mk' _).comp (ι v.1)
  have hΦ : ∀ (m : M₁.carrier) (v : S), Φ m v = 0 ↔ toLocal v.1 (m : V) ∈ localLattice v.1 M₂.carrier := by
    intro m v
    show QuotientAddGroup.mk' _ (ι v.1 m) = 0 ↔ _
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hker : Φ.ker = (M₂.carrier.comap M₁.carrier.subtype).toAddSubgroup := by
    ext m
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      Submodule.coe_subtype]
    constructor
    · intro h
      refine mem_of_forall_toLocal_mem M₂ fun v => ?_
      by_cases hv : v ∈ S
      · exact (hΦ m ⟨v, hv⟩).mp (congrFun h ⟨v, hv⟩)
      · exact hout v hv (subset_span ⟨m, m.2, rfl⟩)
    · intro h
      funext v
      exact (hΦ m v).mpr (subset_span ⟨m, h, rfl⟩)
  have hsurj : Function.Surjective Φ := by
    intro q
    choose y hy using fun v : S => QuotientAddGroup.mk'_surjective _ (q v)
    obtain ⟨x, hx, hnear⟩ := exists_mem_near M₁.carrier M₁.fg S b hb
      (fun v => if h : v ∈ S then ((y ⟨v, h⟩ : A v) : v.adicCompletion K ⊗[K] V) else 0)
      (fun v hv => by simp only [dif_pos hv]; exact (y ⟨v, hv⟩).2)
    refine ⟨⟨x, hx⟩, funext fun v => ?_⟩
    rw [← hy v]
    show QuotientAddGroup.mk' _ (ι v.1 ⟨x, hx⟩) = _
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    obtain ⟨w, hw, hxw⟩ := hnear v.1 v.2
    rw [dif_pos v.2] at hxw
    have e : ((-(ι v.1 ⟨x, hx⟩) + y v : A v.1) : v.1.adicCompletion K ⊗[K] V) =
        -(algebraMap K (v.1.adicCompletion K) (b : K) • w) := by
      rw [← hxw]
      push_cast
      show -(toLocal v.1 x) + _ = _
      abel
    show _ ∈ localLattice v.1 M₂.carrier
    rw [e]
    exact neg_mem (LatticeOfLocalisations.smul_localLattice_mem v.1 b hbM' hw)
  have hcard : Nat.card (M₁.carrier ⧸ M₂.carrier.comap M₁.carrier.subtype) =
      ∏ v : S, Nat.card (A v.1 ⧸ (B v.1).addSubgroupOf (A v.1)) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).toEquiv.trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).toEquiv)
  rw [hcard, Nat.cast_prod, finprod_eq_prod_of_mulSupport_subset (s := S), ← Finset.prod_coe_sort S]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    have h1 : (localLattice v M₂.carrier).toAddSubgroup.relIndex
        (localLattice v M₁.carrier).toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.mpr fun y hy => hout v hvS hy
    simp only [h1, Nat.cast_one]

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
