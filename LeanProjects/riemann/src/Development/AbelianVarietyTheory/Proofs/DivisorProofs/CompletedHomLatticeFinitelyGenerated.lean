import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatFinGen

open GlobalTheory.LatVac GlobalTheory.LatFinMod

theorem pair_smul_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (α : Af F) (x : E) :
    algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 α) * (pairA F 0 1 ⊗ₜ[F] x) = pairA F 0 α ⊗ₜ[F] x := by
  have hp : pairA F 0 α * pairA F 0 1 = pairA F 0 α := Prod.ext (mul_zero _) (mul_one _)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact congrArg (· ⊗ₜ[F] x) hp

theorem smul_finTens_one {D : D7} {m n : ℕ} (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • finTens 1 M = finTens α M :=
  Matrix.ext fun i j => pair_smul_tmul α (M i j)

theorem latO_finitely_generated : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U := by
  intro D S T ΛS ΛT hS hT
  obtain ⟨A, hA, hA1, hA2⟩ := exists_int_gen (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl _)
  obtain ⟨B, hB, hB1, hB2⟩ := exists_int_gen ΛS hS.1.fg
  obtain ⟨C, hC, hC1, hC2⟩ := exists_int_gen ΛT hT.1.fg
  refine ⟨finTens 1 '' ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)),
    ((hA.prod (hB.prod hC)).image _).image _, ?_, fun U hU u hu => ?_⟩
  · rintro _ ⟨_, ⟨⟨a, s, t⟩, ⟨ha, hs, ht⟩, rfl⟩, rfl⟩
    refine AddSubgroup.subset_closure ⟨1, fun v => ?_, fun v hv => absurd trivial hv,
      a, hA1 ha, s, hB1 hs, t, hC1 ht, rfl⟩
    rw [map_one]; exact one_mem _
  · refine (AddSubgroup.closure_le U).2 ?_ hu
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    let φ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[ℤ] WO S T :=
      (AddMonoidHom.mk' (finTens α) (finTens_add α)).toIntLinearMap
    have hle : Submodule.span ℤ ((fun p : _ × _ × _ => genMap S T p.1 p.2.1 p.2.2) '' (A ×ˢ B ×ˢ C)) ≤
        U.toIntSubmodule.comap φ := by
      refine Submodule.span_le.2 fun M hM => ?_
      have := hU α hα _ ⟨M, hM, rfl⟩
      rw [smul_finTens_one] at this
      exact this
    exact hle (genMap_mem_span S T (hA2 _ ha) (hB2 _ hs) (hC2 _ ht))

end GlobalTheory.LatFinGen

end
