import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.LamEig2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open UpperTheory.V.Z.Kato.Joint
open scoped Pointwise

private theorem aqBd_place {q : ℕ} (hq : q.Prime) : ∃ w : Pl, ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by
  have hn : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) = q := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hne : Ideal.span {((q : ℕ) : 𝓞 ℚ)} ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hn
    exact hq.one_lt.ne hn
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((q : ℕ) : 𝓞 ℚ) ∈ M := (Ideal.span_singleton_le_iff_mem M).1 hle
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hq.ne_zero (Nat.cast_eq_zero.1 hmem)

private theorem aqBd_frob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {q : ℕ} (hq : q.Prime) :
    ∃ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s := by
  obtain ⟨w, hw⟩ := aqBd_place hq
  obtain ⟨V, hV⟩ := exists_isPlaceOver (F := ℚ) Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hV
  rw [GlobalTheory.RhoAdm.normV_ratPrime hq w hw] at hσ
  refine ⟨σ, V, ?_, fun x hx => ⟨?_, hσ.2 x ((V.valuation_le_one_iff x).2 hx)⟩⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    simpa using (hV _).2 hw
  · have h : σ • V = V := MulAction.mem_stabilizer_iff.1 hσ.1
    rw [← h]
    exact ValuationSubring.smul_mem_pointwise_smul σ x V hx

theorem UpperTheory.V.Z.Kato.Joint.aqBd :
    UpperTheory.V.Z.Kato.Joint.AqBd := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hχ hatt
  obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
  have hc := (Continuous.matrix_trace
    (Units.continuous_val.comp (GlobalTheory.RhoAdm.untw_cont e W χ hN.cont hχ))).norm
  haveI : CompactSpace (Ω ≃ₐ[ℚ] Ω) := inferInstance
  obtain ⟨C, hC⟩ := (isCompact_range hc).bddAbove
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (max C (∑ q ∈ S0, ‖ι.symm (g.a q)‖))
  refine ⟨k, fun q hq => le_trans ?_ hk⟩
  by_cases hqS : q ∈ S0
  · exact le_max_of_le_right
      (Finset.single_le_sum (f := fun q => ‖ι.symm (g.a q)‖) (fun _ _ => norm_nonneg _) hqS)
  · obtain ⟨s, hs⟩ := aqBd_frob Ω hq
    rw [← (hS0 q hq hqS s hs).1]
    exact le_max_of_le_left (hC ⟨s, rfl⟩)
