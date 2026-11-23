import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealMemIffOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealCountLeOrder
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.LatLine

theorem smul_one_tmul_mem_latLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
    ∀ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 → (∀ c : E, c ∈ I ↔ c • u ∈ L) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v ⊗[F] E),
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
          GlobalTheory.UnrTate.valAt v w c ≤ WithZero.exp (-FractionalIdeal.count E w I)) →
      (c • fun i => (1 : Fv F v) ⊗ₜ[F] u i) ∈ latLoc F L v := by
  intro F E _ _ _ _ _ n L _ u _ I hI hIu v c hc
  set U : Fin n → Fv F v ⊗[F] E := fun i => (1 : Fv F v) ⊗ₜ[F] u i with hU
  have key : ∀ z ∈ I * I⁻¹, (c * (1 : Fv F v) ⊗ₜ[F] z) • U ∈ latLoc F L v := by
    intro z hz
    refine FractionalIdeal.mul_induction_on hz (fun i hi j hj => ?_) (fun x y hx hy => ?_)
    · have hint : c * (1 : Fv F v) ⊗ₜ[F] j ∈ GlobalTheory.AdelicU.intLoc F E v := by
        refine GlobalTheory.TateUnr.mem_intLoc_of_toCompl fun w hw => ?_
        have h2 : Valued.v (algebraMap E (w.adicCompletion E) j) = w.valuation E j :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w j
        have h3 := hc w hw
        rw [GlobalTheory.UnrTate.valAt_of_under hw] at h3
        rw [map_mul, map_mul, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul, h2]
        calc Valued.v (GlobalTheory.LFun.toCompl hw c) * w.valuation E j
            ≤ WithZero.exp (-FractionalIdeal.count E w I) * WithZero.exp (-FractionalIdeal.count E w I⁻¹) :=
              mul_le_mul' h3 (GlobalTheory.UnrTate.valuation_le_of_mem w hj)
          _ = 1 := by
              rw [FractionalIdeal.count_inv, neg_neg, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      have hiu : (i • u) ∈ L := (hIu i).1 hi
      have hmem : (fun k => (1 : Fv F v) ⊗ₜ[F] (i • u) k) ∈ latLoc F L v :=
        GlobalTheory.AdelicU.tmul_mem_latLoc (one_mem _) hiu
      have hs := (latLoc F L v).smul_mem (⟨_, hint⟩ : GlobalTheory.AdelicU.intLoc F E v) hmem
      convert hs using 1
      funext k
      simp only [hU, Pi.smul_apply, smul_eq_mul, Submodule.coe_smul]
      change c * (1 : Fv F v) ⊗ₜ[F] (i * j) * (1 : Fv F v) ⊗ₜ[F] u k
        = c * (1 : Fv F v) ⊗ₜ[F] j * (1 : Fv F v) ⊗ₜ[F] (i * u k)
      rw [mul_assoc, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm i j, mul_assoc]
    · rw [TensorProduct.tmul_add, mul_add, add_smul]; exact add_mem hx hy
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  have := key 1 h1
  rwa [← Algebra.TensorProduct.one_def, mul_one] at this

end GlobalTheory.LatLine
