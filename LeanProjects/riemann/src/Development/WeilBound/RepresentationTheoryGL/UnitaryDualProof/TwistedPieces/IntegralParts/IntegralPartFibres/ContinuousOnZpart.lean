import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ZpartUnique
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CompactPowers.ExistsPowSmulMemOfIsCompact

noncomputable section

open Matrix ValuativeRel Topology Filter Set
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.T.Nil.Orb.Ozn

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem exists_cpt {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {K : Set (Matrix (Fin n) (Fin n) k)}
    (hK : IsCompact K) : ∃ S : Set (Matrix (Fin n) (Fin n) k), IsCompact S ∧ S ⊆ Z ∧ ∀ x ∈ K ∩ CC Z, zpart Z x ∈ S := by
  obtain ⟨T, hT⟩ := exists_bound hZ hK
  have hu : (ϖ k ^ T) ≠ 0 := pow_ne_zero _ (ϖ_ne_zero)
  refine ⟨(fun M => (ϖ k ^ T)⁻¹ • M) '' (ball n 1 ∩ (Z : Set (Matrix (Fin n) (Fin n) k))), ?_, ?_, ?_⟩
  · exact ((isCompact_ball 1).inter_right (isClosed_subalgebra Z)).image (continuous_const_smul _)
  · rintro _ ⟨M, ⟨_, hM⟩, rfl⟩
    exact Z.smul_mem hM _
  · intro x hx
    obtain ⟨hc, hnil⟩ := zpart_spec hx.2
    refine ⟨ϖ k ^ T • zpart Z x, ⟨hT _ hc _ hnil (by simpa using hx.1), Z.smul_mem hc _⟩, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ hu, one_smul]

theorem continuousOn_zpart {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) : ContinuousOn (zpart Z) (CC Z) := by
  intro x hx
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨S, hS, hSZ, hSK⟩ := exists_cpt hZ hK
  have hmem : ∀ᶠ y in 𝓝[CC Z] x, zpart Z y ∈ S := by
    filter_upwards [nhdsWithin_le_nhds hKx, self_mem_nhdsWithin] with y hy1 hy2
    exact hSK y ⟨hy1, hy2⟩
  refine hS.tendsto_nhds_of_unique_mapClusterPt hmem ?_
  intro c hcS hcl
  refine zpart_unique hZ hx.2 (hSZ hcS) ?_ |>.symm
  by_contra hne
  have hU : IsOpen {p : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k | ¬IsNilpotent (p.1 - p.2)} :=
    (isClosed_nilpotent.preimage (continuous_fst.sub continuous_snd)).isOpen_compl
  obtain ⟨A, B, hA, hB, hxA, hcB, hAB⟩ := isOpen_prod_iff.1 hU x c hne
  have hev : ∀ᶠ y in 𝓝[CC Z] x, y ∈ A ∧ y ∈ CC Z := by
    filter_upwards [nhdsWithin_le_nhds (hA.mem_nhds hxA), self_mem_nhdsWithin] with y h1 h2
    exact ⟨h1, h2⟩
  have hfr : ∃ᶠ y in 𝓝[CC Z] x, zpart Z y ∈ B := (mapClusterPt_iff_frequently.1 hcl) B (hB.mem_nhds hcB)
  obtain ⟨y, hyB, hyA, hyC⟩ := (hfr.and_eventually hev).exists
  exact hAB (Set.mk_mem_prod hyA hyB) (zpart_spec hyC).2

end PositivityTheory.RgUd.TP.Nil.Fib1
