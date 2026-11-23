import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section AvgAux

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem avg_shift {K : Subgroup G} (M : Subgroup K) [M.Normal] [Fintype (K ⧸ M)]
    (π : Representation ℂ G V) (θ : G → ℂ) (s : K ⧸ M → K)
    (hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q) (hone : θ 1 = 1)
    (hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b)
    (w : V) (hw : ∀ m ∈ M, π (m : G) w = w) (hθM : ∀ m ∈ M, θ (m : G) = 1) (h : K) :
    ∑ q, (θ (s q))⁻¹ • π (s q) (π h w) = θ h • ∑ q, (θ (s q))⁻¹ • π (s q) w := by
  have hne : ∀ a : K, θ a ≠ 0 := by
    intro a ha
    have := hmul a a⁻¹
    rw [mul_inv_cancel, ha, zero_mul] at this
    simp [hone] at this
  have key : ∀ q : K ⧸ M, (θ (s q))⁻¹ • π (s q) (π h w) =
      θ h • ((θ (s (q * QuotientGroup.mk h)))⁻¹ • π (s (q * QuotientGroup.mk h)) w) := by
    intro q
    set q' := q * (QuotientGroup.mk h : K ⧸ M)
    set m : K := (s q')⁻¹ * (s q * h) with hm_def
    have hmM : m ∈ M := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [hm_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, q']
      group
    have hsplit : s q * h = s q' * m := by simp [hm_def]
    have h1 : π (s q) (π h w) = π (s q') w := by
      have : π ((s q * h : K) : G) w = π ((s q' * m : K) : G) w := by rw [hsplit]
      simpa [map_mul, hw m hmM] using this
    have h2 : θ (s q) * θ h = θ (s q') := by
      rw [← hmul, hsplit, hmul, hθM m hmM, mul_one]
    rw [h1, smul_smul]
    congr 1
    rw [← h2]
    field_simp [hne (s q), hne h]
  rw [Finset.sum_congr rfl fun q _ => key q, ← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk h : K ⧸ M))
    (fun q => (θ (s q))⁻¹ • π (s q) w)

end AvgAux

theorem aug_avg_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧
      ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  intro G V _ _ _ _ _ π hsm H θ hD u hu
  let K : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hu
  choose h hh w hw using fun i => (g i).2
  have hmul : ∀ a b : K, θ ((a * b : K) : G) = θ a * θ b := fun a b => hD.val_mul a a.2 b b.2
  let N : Subgroup K :=
    { carrier := {j | θ j = 1 ∧ ∀ i, π j (w i) = w i}
      mul_mem' := by
        intro a b ha hb
        refine ⟨by rw [hmul, ha.1, hb.1, one_mul], fun i => ?_⟩
        simp [map_mul, ha.2 i, hb.2 i]
      one_mem' := ⟨hD.val_one, fun i => by simp⟩
      inv_mem' := by
        intro a ha
        refine ⟨?_, fun i => ?_⟩
        · have := hmul a a⁻¹
          rw [mul_inv_cancel, ha.1, one_mul] at this
          simpa [hD.val_one] using this.symm
        · have := congrArg (π ((a⁻¹ : K) : G)) (ha.2 i)
          simpa [← map_mul] using this.symm }
  have hNopen : IsOpen (N : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds
    obtain ⟨U, hU, hUθ⟩ := hD.near
    have hS : (U ∩ ⋂ i, {g : G | π g (w i) = w i}) ∈ nhds (1 : G) :=
      Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (hsm (w i)).mem_nhds (by simp))
    have hS' := continuous_subtype_val.continuousAt.preimage_mem_nhds (x := (1 : K)) hS
    refine Filter.mem_of_superset hS' ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
    exact ⟨hUθ x hx.1 x.2, hx.2⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (show IsCompact (K : Set G) from hD.compact)
  haveI : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let M : Subgroup K := N.normalCore
  haveI : Finite (K ⧸ M) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (K ⧸ M) := Fintype.ofFinite _
  classical
  let s : K ⧸ M → K := fun q => if q = 1 then 1 else q.out
  have hs : ∀ q, (QuotientGroup.mk (s q) : K ⧸ M) = q := by
    intro q
    by_cases hq : q = 1
    · simp [s, hq]
    · simp [s, hq]
  have hMN : ∀ m ∈ M, m ∈ N := fun m hm => Subgroup.normalCore_le N hm
  have hinj : Function.Injective (fun q => ((s q : K) : G)) := by
    intro a b hab
    rw [← hs a, ← hs b, Subtype.ext hab]
  refine ⟨Finset.univ.image (fun q => ((s q : K) : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [s]⟩
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (s q).2
  · rw [Finset.sum_image fun a _ b _ hab => hinj hab]
    have hgen : ∀ i, ∑ q, (θ (s q))⁻¹ • π (s q) ((g i : V)) = 0 := by
      intro i
      rw [hw i]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib]
      have := avg_shift M π θ s hs hD.val_one hmul (w i) (fun m hm => (hMN m hm).2 i)
        (fun m hm => (hMN m hm).1) ⟨h i, hh i⟩
      rw [this, Finset.smul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_comm]
    simp only [map_sum, map_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hc : ∀ q, (θ (s q : G))⁻¹ • c i • π (s q : G) (g i : V) =
        c i • ((θ (s q : G))⁻¹ • π (s q : G) (g i : V)) := fun q => smul_comm _ _ _
    simp only [hc, ← Finset.smul_sum, hgen i, smul_zero]

end GlobalTheory.PsType
