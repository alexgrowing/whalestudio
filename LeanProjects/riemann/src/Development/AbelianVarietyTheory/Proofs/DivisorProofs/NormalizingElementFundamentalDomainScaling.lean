import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas

namespace GlobalTheory.SupMeas

theorem isFundamentalDomain_conj_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N Q : Subgroup G) (m : G) (_hN : IsClosed (N : Set G))
    (hm : ∀ n ∈ N, m * n * m⁻¹ ∈ N ∧ m⁻¹ * n * m ∈ N) (νN : Measure N) (E : Set N)
    (hE : IsFundamentalDomain (Q.subgroupOf N) E νN) (c : ENNReal) (hc : c ≠ 0)
    (hmod : ∀ S : Set N,
      c * νN (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S))) = νN S) :
    IsFundamentalDomain ((Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf N)
      (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' E))) νN := by
  let f : N → N := fun x => ⟨m * x * m⁻¹, (hm x x.2).1⟩
  have hset : ∀ S : Set N,
      Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S)) = f ⁻¹' S := by
    intro S; ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      have h1 : (y : G) = m * x * m⁻¹ := by rw [← hyx]; group
      have h2 : y = f x := Subtype.ext h1
      rwa [← h2]
    · intro hx
      exact ⟨_, ⟨_, hx, rfl⟩, by simp [f, mul_assoc]⟩
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    fun_prop
  have hfm : Measurable f := hfc.measurable
  have hq : Measure.QuasiMeasurePreserving f νN νN := by
    refine ⟨hfm, ?_⟩
    refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
    rw [Measure.map_apply hfm hS, ← hset]
    have h3 := hmod S
    rw [h0] at h3
    exact (mul_eq_zero.mp h3).resolve_left hc
  have hmemQ : ∀ l : Q.subgroupOf N, m⁻¹ * ((l : N) : G) * m ∈ Q.map (MulAut.conj m⁻¹).toMonoidHom := by
    intro l
    refine Subgroup.mem_map.mpr ⟨((l : N) : G), (Subgroup.mem_subgroupOf.mp l.2), ?_⟩
    simp
  let e : Q.subgroupOf N → (Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf N := fun l =>
    ⟨⟨m⁻¹ * ((l : N) : G) * m, (hm _ (l : N).2).2⟩, Subgroup.mem_subgroupOf.mpr (hmemQ l)⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      have h4 : m⁻¹ * ((a : N) : G) * m = m⁻¹ * ((b : N) : G) * m := by
        simpa [e] using congrArg (fun z : (Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf N => ((z : N) : G)) hab
      exact Subtype.ext (Subtype.ext (by simpa using h4))
    · intro h
      obtain ⟨q, hqQ, hqh⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp h.2)
      have hq' : m⁻¹ * q * m = ((h : N) : G) := by simpa using hqh
      have hqN : q ∈ N := by
        have h5 : q = m * ((h : N) : G) * m⁻¹ := by rw [← hq']; group
        rw [h5]; exact (hm _ (h : N).2).1
      refine ⟨⟨⟨q, hqN⟩, Subgroup.mem_subgroupOf.mpr hqQ⟩, ?_⟩
      exact Subtype.ext (Subtype.ext (by simpa [e] using hq'))
  rw [hset E]
  refine hE.preimage_of_equiv hq he ?_
  intro l x
  apply Subtype.ext
  simp only [Subgroup.smul_def, smul_eq_mul, f, e, Subgroup.coe_mul]
  group

end GlobalTheory.SupMeas
