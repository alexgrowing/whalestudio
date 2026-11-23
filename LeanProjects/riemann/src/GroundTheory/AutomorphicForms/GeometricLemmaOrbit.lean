import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Topology Set DoubleCoset

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]

section Action

variable (P Q : Subgroup G) (x : G)

@[instance_reducible]
def doubleCosetAction : MulAction (P × Q) (doubleCoset x (P : Set G) Q) where
  smul pq g := ⟨(pq.1 : G) * g * (pq.2 : G)⁻¹, by
    obtain ⟨p, hp, q, hq, h⟩ := mem_doubleCoset.1 g.2
    refine mem_doubleCoset.2 ⟨pq.1 * p, P.mul_mem pq.1.2 hp, q * (pq.2 : G)⁻¹,
      Q.mul_mem hq (Q.inv_mem pq.2.2), ?_⟩
    rw [h]
    group⟩
  one_smul g := Subtype.ext (by
    show ((1 : P × Q).1 : G) * g * ((1 : P × Q).2 : G)⁻¹ = g
    simp)
  mul_smul a b g := Subtype.ext (by
    show ((a * b).1 : G) * g * ((a * b).2 : G)⁻¹ =
      (a.1 : G) * ((b.1 : G) * g * (b.2 : G)⁻¹) * (a.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_inv_rev]
    group)

end Action

variable {P Q : Subgroup G}

theorem isOpenMap_doubleCoset (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) (x : G)
    (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q)) :
    IsOpenMap (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) := by
  let := doubleCosetAction P Q x
  have : SigmaCompactSpace P := hP.sigmaCompactSpace
  have : SigmaCompactSpace Q := hQ.sigmaCompactSpace
  have : LocallyCompactSpace (doubleCoset x (P : Set G) Q) := hC.locallyCompactSpace
  have : ContinuousSMul (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨Continuous.subtype_mk ?_ _⟩
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv)
  have : MulAction.IsPretransitive (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := mem_doubleCoset.1 a.2
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := mem_doubleCoset.1 b.2
    refine ⟨(⟨p₂ * p₁⁻¹, P.mul_mem hp₂ (P.inv_mem hp₁)⟩, ⟨q₂⁻¹ * q₁, Q.mul_mem (Q.inv_mem hq₂) hq₁⟩), ?_⟩
    apply Subtype.ext
    show (p₂ * p₁⁻¹) * (a : G) * (q₂⁻¹ * q₁)⁻¹ = b
    rw [h₁, h₂]
    group
  have hopen := isOpenMap_smul_of_sigmaCompact (G := P × Q) (X := doubleCoset x (P : Set G) Q)
    ⟨x, mem_doubleCoset_self P Q x⟩
  let e : (P × Q) ≃ₜ (P × Q) := (Homeomorph.refl P).prodCongr (Homeomorph.inv Q)
  have : (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) =
      (fun γ : P × Q => γ • (⟨x, mem_doubleCoset_self P Q x⟩ : doubleCoset x (P : Set G) Q)) ∘ e := by
    funext pq
    apply Subtype.ext
    show (pq.1 : G) * x * pq.2 = (pq.1 : G) * x * ((pq.2⁻¹ : Q) : G)⁻¹
    simp
  rw [this]
  exact hopen.comp e.isOpenMap

theorem exists_nhds_inter_doubleCoset_subset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {y : G} (hy : y ∈ doubleCoset x (P : Set G) Q) {UP UQ : Set G} (hUP : UP ∈ 𝓝 (1 : G))
    (hUQ : UQ ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 y, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ UP ∧ ∃ q ∈ Q, q ∈ UQ ∧ z = p * y * q := by
  have hCy : doubleCoset y (P : Set G) Q = doubleCoset x (P : Set G) Q := doubleCoset_eq_of_mem hy
  rw [← hCy] at hC ⊢
  have hopen := isOpenMap_doubleCoset hP hQ y hC
  set W : Set (P × Q) := {pq | (pq.1 : G) ∈ interior UP ∧ (pq.2 : G) ∈ interior UQ}
  have hW : IsOpen W :=
    (isOpen_interior.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isOpen_interior.preimage (continuous_subtype_val.comp continuous_snd))
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (hopen W hW)
  have h1 : (1 : P × Q) ∈ W := ⟨mem_interior_iff_mem_nhds.2 hUP, mem_interior_iff_mem_nhds.2 hUQ⟩
  have hyV : y ∈ V := by
    have : (⟨y, mem_doubleCoset_self P Q y⟩ : doubleCoset y (P : Set G) Q) ∈
        Subtype.val ⁻¹' V := by
      rw [hV]
      exact ⟨1, h1, Subtype.ext (by simp)⟩
    exact this
  refine ⟨V, hVo.mem_nhds hyV, fun z hz hzC => ?_⟩
  have : (⟨z, hzC⟩ : doubleCoset y (P : Set G) Q) ∈ Subtype.val ⁻¹' V := hz
  rw [hV] at this
  obtain ⟨pq, hpq, hpqz⟩ := this
  refine ⟨pq.1, pq.1.2, interior_subset hpq.1, pq.2, pq.2.2, interior_subset hpq.2, ?_⟩
  exact (congrArg Subtype.val hpqz).symm

theorem exists_isCompact_subset_doubleCoset (hP : IsClosed (P : Set G))
    (hQ : IsClosed (Q : Set G)) {x : G} (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q))
    {Kc : Set G} (hK : IsCompact Kc) (hKC : Kc ⊆ doubleCoset x (P : Set G) Q) :
    ∃ L : Set G, IsCompact L ∧ L ⊆ Q ∧ ∀ z ∈ Kc, ∃ p ∈ P, ∃ l ∈ L, z = p * x * l := by
  obtain ⟨K₁, hK₁c, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hloc : ∀ c ∈ Kc, ∃ V ∈ 𝓝 c, ∀ z ∈ V, z ∈ doubleCoset x (P : Set G) Q →
      ∃ p ∈ P, p ∈ (univ : Set G) ∧ ∃ q ∈ Q, q ∈ K₁ ∧ z = p * c * q :=
    fun c hc => exists_nhds_inter_doubleCoset_subset hP hQ hC (hKC hc) Filter.univ_mem hK₁
  choose V hV hVsub using hloc
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' V hV
  have hq : ∀ c : Kc, ∃ p ∈ P, ∃ q ∈ Q, (c : G) = p * x * q := fun c => mem_doubleCoset.1 (hKC c.2)
  choose pc hpc qc hqc hcq using hq
  refine ⟨⋃ c ∈ t, (fun z => qc c * z) '' ((Q : Set G) ∩ K₁), ?_, ?_, ?_⟩
  · exact t.isCompact_biUnion fun c _ =>
      (hK₁c.inter_left hQ).image (continuous_const.mul continuous_id)
  · intro l hl
    simp only [Set.mem_iUnion, Set.mem_image] at hl
    obtain ⟨c, _, z, hz, rfl⟩ := hl
    exact Q.mul_mem (hqc c) hz.1
  · intro z hz
    have hz' := ht hz
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨c, hct, hzc⟩ := hz'
    obtain ⟨p, hp, -, q, hq, hqK, rfl⟩ := hVsub c c.2 z hzc (hKC hz)
    refine ⟨p * pc c, P.mul_mem hp (hpc c), qc c * q, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_image]
      exact ⟨c, hct, q, ⟨hq, hqK⟩, rfl⟩
    · rw [hcq c]
      group

end Parabolic

end GroundTheory.Automorphic
