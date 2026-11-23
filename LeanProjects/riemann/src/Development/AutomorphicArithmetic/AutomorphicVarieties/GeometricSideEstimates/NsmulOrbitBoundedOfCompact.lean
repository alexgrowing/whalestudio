import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.InfinitePlaceNormContinuity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum Filter Topology

private theorem nsmul_mem_of_compact {E : Type} [Field E] [NumberField E] {a : ℕ} (L : AddSubgroup (Fin a → Af E))
    (hL : IsOpen (L : Set (Fin a → Af E))) {T : Set (Fin a → Af E)} (hT : IsCompact T) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ T, M • x ∈ L := by
  have hc : Continuous fun p : Af E × (Fin a → Af E) => p.1 • p.2 := continuous_fst.smul continuous_snd
  have hev : ∀ᶠ r in 𝓝 (0 : Af E), ∀ x ∈ T, r • x ∈ L := by
    refine hT.eventually_forall_of_forall_eventually fun x _ => ?_
    refine hc.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
    show (0 : Af E) • x ∈ L
    rw [zero_smul]
    exact L.zero_mem
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually hev).exists
  refine ⟨n.factorial, n.factorial_pos, fun x hx => ?_⟩
  have h := hn x hx
  rwa [Nat.cast_smul_eq_nsmul] at h

theorem UpperTheory.nsmul_orbit_bounded_of_compact :
    ShortRow := by
  intro E _ _ _ a ha L hL
  obtain ⟨T, C, N, hT, hrow⟩ := UpperTheory.infinite_place_norm_continuity E a ha
  obtain ⟨M, hM, hML⟩ := nsmul_mem_of_compact L hL.isOpen hT
  refine ⟨((M : ℝ) ^ 2) ^ N * C, N, fun g => ?_⟩
  obtain ⟨-, hq, hF⟩ := (UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha).2.1 g
  obtain ⟨v, hv, hvT, hvC⟩ := hrow (retractOne g)
  change ptF (rt g) v ∈ T at hvT
  change qht (rt g) * qf (pt (rt g) v) ^ N ≤ C at hvC
  rw [hF] at hvT
  rw [hq] at hvC
  refine ⟨M • v, ?_, ?_, ?_⟩
  · show ptF g (M • v) ∈ L
    rw [map_nsmul]
    exact hML _ hvT
  · rw [← Nat.cast_smul_eq_nsmul E]
    exact smul_ne_zero (Nat.cast_ne_zero.2 hM.ne') hv
  · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, (UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.1, mul_pow, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hvC (by positivity)
