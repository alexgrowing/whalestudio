import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.evalBasis_pf :
    EvalBasis := by
  intro X V _ _ ev hsep W hW
  classical
  haveI := hW
  let r : X → Module.Dual ℂ W := fun x => (ev x).domRestrict W
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ W).surjective f
    have hv : (v : V) = 0 := hsep v fun x => by
      have h := hf (Submodule.subset_span (Set.mem_range_self x))
      simpa [r] using h
    have hv0 : v = 0 := Subtype.ext hv
    exact hf0 (by simp [hv0])
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℂ (Set.range r)
  let B0 := Module.Basis.mk hli (by simp [hbspan, hspan])
  haveI : Finite b := Module.Finite.finite_basis B0
  letI := Fintype.ofFinite b
  let B := B0.reindex (Fintype.equivFin b)
  have hx : ∀ i, ∃ x, r x = B i := fun i => by
    have hm : B i ∈ b := by simp [B, B0]
    exact hbs hm
  choose x hx using hx
  refine ⟨Fintype.card b, x, fun i => ((Module.evalEquiv ℂ W).symm (B.coord i) : W),
    fun i => Subtype.coe_prop _, fun v hv => ?_⟩
  have key : (⟨v, hv⟩ : W) = ∑ i, (B i ⟨v, hv⟩) • (Module.evalEquiv ℂ W).symm (B.coord i) := by
    apply (Module.evalEquiv ℂ W).injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    exact (B.sum_dual_apply_smul_coord _).symm
  have h2 := congrArg (Subtype.val) key
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hx i]
  rfl
