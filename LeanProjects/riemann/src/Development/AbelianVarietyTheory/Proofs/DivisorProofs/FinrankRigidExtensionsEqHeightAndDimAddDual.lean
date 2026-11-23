import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeCotangentDimAddDualCotangentDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeightStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finite_omega_of_eq_zero {p : ℕ} {K : Type} [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) : Module.Finite K G.omega := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm

theorem finrank_rigExt_omega (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) :
    Module.Finite K G.omega ∧ Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
      Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  have h1 := finite_omega_of_eq_zero h G
  have h2 := finite_omega_of_eq_zero h G.dual
  have e1 : Module.finrank K G.omega = Module.finrank K (Cot K (G.A 1)) :=
    (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).finrank_eq
  have e2 : Module.finrank K G.dual.omega = Module.finrank K (Cot K (G.dual.A 1)) :=
    (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective h)).finrank_eq
  have hsum : Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
    rw [e1, e2]
    exact le_antisymm (GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height p K h G) (GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim p K h G)

  have hr := (G.rigToLie h).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), rank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    (LinearEquiv.ofInjective _ (G.rigOfOmega_injective_of_eq_zero h)).rank_eq.symm] at hr
  have hfin : Module.Finite K G.RigExt := by
    haveI : Module.Free K G.RigExt := Module.Free.of_divisionRing K _
    rw [← Module.rank_lt_aleph0_iff, ← hr]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 K _) (Module.rank_lt_aleph0 K _)
  refine ⟨h1, hfin, ?_, hsum⟩
  have e := (G.rigToLie h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), finrank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    LinearMap.finrank_range_of_inj (G.rigOfOmega_injective_of_eq_zero h)] at e
  rw [← e, ← hsum, add_comm, Subspace.dual_finrank_eq]

end GlobalTheory.PDivGroup
