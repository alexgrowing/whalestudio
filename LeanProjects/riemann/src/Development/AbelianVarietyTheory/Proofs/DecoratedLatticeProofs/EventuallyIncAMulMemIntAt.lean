import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AeUnit

theorem idem_mul_finPart (D : D7) (v : Pl D) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a = finPart D a := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
  rw [map_mul, Algebra.TensorProduct.map_tmul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, map_one, ← Algebra.TensorProduct.one_def, one_mul]
  · have h0 : GlobalTheory.FinPl.compAt D w a = 0 := (Submodule.mem_iInf _).1 ha.2 ⟨w, hw⟩
    have h1 : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (finPart D a) = 0 := h0
    rw [h1, mul_zero]

theorem inv_smul_singleV_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℤ)
    (h : (N : 𝓞 F) ∉ v.asIdeal) : (N : F)⁻¹ • singleV F v 1 ∈ intAf F := by
  intro w
  rw [map_smul]
  by_cases hw : w = v
  · subst hw
    rw [GlobalTheory.LatVac.evalV_singleV_same, ← Algebra.algebraMap_eq_smul_one,
      HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : w.valuation F (algebraMap (𝓞 F) F N) = 1 := (w.valuation_eq_one_iff_notMem (K := F)).2 h
    rw [map_intCast] at h1
    have h2 : Valued.v (algebraMap F (Fv F w) (N : F)⁻¹) = w.valuation F (N : F)⁻¹ :=
      w.valuedAdicCompletion_eq_valuation' _
    rw [h2, map_inv₀, h1, inv_one]
  · rw [GlobalTheory.LatVac.evalV_singleV_ne F v w hw, smul_zero]
    exact zero_mem _

theorem tmul_eq_inv_smul_tmul {F M P : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup P] [Module F P]
    (N : ℤ) (hN : (N : F) ≠ 0) (x : M) (c : P) : x ⊗ₜ[F] c = ((N : F)⁻¹ • x) ⊗ₜ[F] (N • c) := by
  rw [TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F N c, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem eventually_incA_mul_mem_intAt : ∀ (D : D7) (c : D.host.E), ∀ᶠ v : Pl D in cofinite,
    ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro D c
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨N, hN, hint⟩ := halg.exists_integral_multiple
  have hN' : (N : 𝓞 D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  have hfin := Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.F)})
    (fun h => hN' (Ideal.span_singleton_eq_bot.1 h))
  filter_upwards [hfin.compl_mem_cofinite] with v hv a ha
  have hv' : (N : 𝓞 D.host.F) ∉ v.asIdeal := fun h => hv (Ideal.dvd_span_singleton.2 h)
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, inv_smul_singleV_mem v N hv', ⟨N • c, hint⟩, ?_⟩
  exact tmul_eq_inv_smul_tmul N hNF _ c

end GlobalTheory.FinPl.AeUnit
