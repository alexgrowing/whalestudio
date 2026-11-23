import Mathlib
import Formalism.PeriodIntegrals.LocHaarRR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.IntegralMemNhdsAndSubsetCompactOfFinrankTwo

noncomputable section

open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField

namespace PI.LocHaarRRW

section Some

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}

theorem mem_ordR (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (h1 : (sg.e x).1 ∈ 𝒪[A.Fp]) (h2 : (sg.e x).2 ∈ 𝒪[A.Fp])
    (h12 : Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).1, h1⟩ =
      Ideal.Quotient.mk (Ideal.span {sg.q}) ⟨(sg.e x).2, h2⟩) :
    x ∈ PI.LocHaarRR.ordR sg := by
  simp only [PI.LocHaarRR.ordR]
  rw [Subring.mem_comap, Subring.mem_map]
  exact ⟨(⟨_, h1⟩, ⟨_, h2⟩), h12, rfl⟩

theorem ordR_sub (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) {x : A.Ep}
    (hx : x ∈ PI.LocHaarRR.ordR sg) : (sg.e x).1 ∈ 𝒪[A.Fp] ∧ (sg.e x).2 ∈ 𝒪[A.Fp] := by
  simp only [PI.LocHaarRR.ordR] at hx
  rw [Subring.mem_comap, Subring.mem_map] at hx
  obtain ⟨y, -, hy⟩ := hx
  have hy' : sg.e x = ((y.1 : A.Fp), (y.2 : A.Fp)) := hy.symm
  rw [hy']
  exact ⟨y.1.2, y.2.2⟩

end Some

theorem target : PI.LocHaarRR.Target := by
  intro F E _ _ _ _ _ sig p A hred
  haveI := A.lf
  haveI := A.top
  haveI := A.borel
  haveI := A.char0
  haveI := A.free
  haveI : IsTopologicalAddGroup A.Ep := IsModuleTopology.topologicalAddGroup A.Fp A.Ep
  haveI := sigmaCompactSpace_lf A.Fp
  rcases hs : A.split with _ | sg
  · obtain ⟨H, h0, C, hC, hOC⟩ := integral_mem_nhds_and_subset_compact_of_finrank_two A.rank A.O A.O_def
    haveI : SigmaCompactSpace A.Ep := H.symm.isClosedEmbedding.sigmaCompactSpace
    have hR : PI.LocHaarRR.RR A = (A.O : Set A.Ep) := by simp [PI.LocHaarRR.RR, hs]
    rw [hR]
    exact exists_haar_of_subgroup A.O.toAddSubgroup h0 hC hOC
  · have hR : PI.LocHaarRR.RR A = (PI.LocHaarRR.ordR sg : Set A.Ep) := by
      simp [PI.LocHaarRR.RR, hs]
    rw [hR]
    let H : A.Fp × A.Fp ≃ₜ A.Ep := homeoOfLin sg.e.symm.toLinearEquiv
    have hH : ∀ y, sg.e (H y) = y := fun y => sg.e.apply_symm_apply y
    have hH' : ∀ x, H (sg.e x) = x := fun x => sg.e.symm_apply_apply x
    haveI : SigmaCompactSpace A.Ep := H.symm.isClosedEmbedding.sigmaCompactSpace
    have hq0 : (sg.q : A.Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
    let Q : Set A.Fp := (fun y : A.Fp => (sg.q : A.Fp) * y) '' (𝒪[A.Fp] : Set A.Fp)
    have hQ : IsOpen Q := (Homeomorph.mulLeft₀ (sg.q : A.Fp) hq0).isOpenMap _ (isOpen_integer' _)
    refine exists_haar_of_subgroup (PI.LocHaarRR.ordR sg).toAddSubgroup ?_
      (((isCompact_integer _).prod (isCompact_integer _)).image H.continuous) ?_
    · rw [mem_nhds_iff]
      refine ⟨H '' (Q ×ˢ Q), ?_, H.isOpenMap _ (hQ.prod hQ), ⟨(0, 0), ⟨⟨0, zero_mem _, by simp⟩,
        ⟨0, zero_mem _, by simp⟩⟩, by have h00 := hH' 0; rw [map_zero] at h00; exact h00⟩⟩
      rintro _ ⟨⟨_, _⟩, ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩⟩, rfl⟩
      have h1 : (sg.e (H ((sg.q : A.Fp) * u, (sg.q : A.Fp) * v))).1 ∈ 𝒪[A.Fp] := by
        rw [hH]; exact mul_mem sg.q.2 hu
      have h2 : (sg.e (H ((sg.q : A.Fp) * u, (sg.q : A.Fp) * v))).2 ∈ 𝒪[A.Fp] := by
        rw [hH]; exact mul_mem sg.q.2 hv
      refine mem_ordR sg h1 h2 ?_
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      refine ⟨⟨u, hu⟩ - ⟨v, hv⟩, Subtype.ext ?_⟩
      simp only [hH, AddSubgroupClass.coe_sub, MulMemClass.coe_mul]
      ring
    · intro x hx
      obtain ⟨h1, h2⟩ := ordR_sub sg hx
      exact ⟨sg.e x, ⟨h1, h2⟩, hH' x⟩

end PI.LocHaarRRW
