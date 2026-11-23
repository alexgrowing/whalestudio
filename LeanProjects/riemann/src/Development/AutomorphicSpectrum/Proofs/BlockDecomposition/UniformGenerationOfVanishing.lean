import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSequenceCoherentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformSpanEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedVanishingSectionsSpanStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem uniformGen_of_gradedNoeth : GradedNoeth → UniformVanishing → UniformGen := by
  intro hN hV A _ _ X _ _ H hH k M T d hM
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := hH.compactSpace
  have hcoh := GlobalTheory.T.kernel_sequence_coherent hM
  obtain ⟨d', hd'⟩ := GlobalTheory.T.uniform_span_eventually (KerSeq.kerOp T hM.comm d) (fun e => (hcoh e).1)
    (GlobalTheory.T.kernel_operators_span_eventually hN hM)
  have hK : OpSeq k (KerSeq.kerSeq T d) (KerSeq.kerOp T hM.comm d) d' :=
    ⟨hcoh, KerSeq.kerOp_comm T hM.comm d, hd'⟩
  obtain ⟨n₀, hn₀⟩ := hV (A := A) H hH k _ _ d' hK
  refine ⟨n₀, fun n hn e he => ?_⟩
  obtain ⟨e₀, rfl⟩ := Nat.exists_eq_add_of_le he
  haveI := GlobalTheory.T.operator_sequence_sum_epi hM e₀
  exact GlobalTheory.T.twisted_vanishing_sections_span (GlobalTheory.lbZPow H n) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n) (fun i => T i (d + e₀))
    (kernel.ι _) (kernel.condition _) (KerSeq.kerSC_shortExact T d e₀) (hn₀ n hn e₀ 1 one_pos)

end GlobalTheory.CompanionTheory.GE
