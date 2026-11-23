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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealCountLeOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LineLocVal

open GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_toCompl_le_one {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (h : w.under (𝓞 F) = v) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Valued.v (toCompl h y) ≤ 1 := by
  refine intLoc_induction (p := fun y => Valued.v (toCompl h y) ≤ 1) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · have h2 : Valued.v (algebraMap E (w.adicCompletion E) (x : E)) = w.valuation E (x : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (x : E)
    rw [toCompl_tmul, map_mul, h2]
    refine mul_le_one' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (complMap_mem h ha)) ?_
    exact HeightOneSpectrum.valuation_le_one w x
  · rw [map_add]; exact (Valuation.map_add_le _ hy hz)
  · rw [map_neg, Valuation.map_neg]; exact hy

theorem toCompl_inclR {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (h : w.under (𝓞 F) = v) (x : E) : toCompl h (inclR (Fv F v) x) = algebraMap E _ x := by
  change toCompl h ((1 : Fv F v) ⊗ₜ[F] x) = _
  rw [toCompl_tmul, map_one, one_mul]

theorem valAt_le_of_smul_mem_latLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
    ∀ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 → (∀ c : E, c ∈ I ↔ c • u ∈ L) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v ⊗[F] E),
      (c • fun i => (1 : Fv F v) ⊗ₜ[F] u i) ∈ latLoc F L v →
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
          GlobalTheory.UnrTate.valAt v w c ≤ WithZero.exp (-FractionalIdeal.count E w I) := by
  intro F E _ _ _ _ _ n L hL u hu I hI hIu v c hc w hw
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  set a : Fin k → E := Φ *ᵥ u with ha
  have hI' : ∀ d : E, d ∈ I ↔ ∀ j, d * a j ∈ (algebraMap (𝓞 E) E).range := fun d => by
    rw [hIu, SelfDual.mem_iff_of_frame h1 hS hΦ, Matrix.mulVec_smul]; rfl
  let J : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanFinset (𝓞 E) Finset.univ a
  have hJmem : ∀ y, y ∈ J ↔ y ∈ Submodule.span (𝓞 E) (a '' (Finset.univ : Finset (Fin k))) := fun y => Iff.rfl
  have ha0 : a ≠ 0 := by
    intro h0
    apply hu
    rw [← Matrix.one_mulVec u, ← h1, ← Matrix.mulVec_mulVec, ← ha, h0, Matrix.mulVec_zero]
  have hJ0 : J ≠ 0 := by
    intro h0
    rw [FractionalIdeal.spanFinset_eq_zero] at h0
    exact ha0 (funext fun j => h0 j (Finset.mem_univ j))
  have hIJ : I = J⁻¹ := by
    ext d
    rw [FractionalIdeal.mem_inv_iff hJ0, hI']
    constructor
    · intro hd y hy
      rw [hJmem] at hy
      rw [FractionalIdeal.mem_one_iff]
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, -, rfl⟩ := hx
        obtain ⟨r, hr⟩ := hd j
        exact ⟨r, hr⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨r, hr⟩ := hx
        obtain ⟨s, hs⟩ := hy
        exact ⟨r + s, by rw [map_add, hr, hs, mul_add]⟩
      | smul r x _ hx =>
        obtain ⟨s, hs⟩ := hx
        exact ⟨r * s, by rw [map_mul, hs, Algebra.smul_def, mul_left_comm]⟩
    · intro hd j
      have := hd (a j) ((hJmem _).2 (Submodule.subset_span ⟨j, Finset.mem_univ j, rfl⟩))
      rw [FractionalIdeal.mem_one_iff] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, hr⟩
  have h1IJ : (1 : E) ∈ I * J := by
    rw [hIJ, inv_mul_cancel₀ hJ0]; exact FractionalIdeal.one_mem_one _
  have hloc : ∀ j, c * inclR (Fv F v) (a j) ∈ intLoc F E v := by
    have := (SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v _).1 hc
    intro j
    have e := this j
    rw [Matrix.mulVec_smul] at e
    have e2 := SelfDual.map_mulVec_inclR (F := F) (Fv F v) Φ u j
    change c * (Φ.map (inclR (Fv F v)) *ᵥ fun i => inclR (Fv F v) (u i)) j ∈ _ at e
    rwa [e2] at e
  have hJloc : ∀ y ∈ J, c * inclR (Fv F v) y ∈ intLoc F E v := by
    intro y hy
    rw [hJmem] at hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨j, -, rfl⟩ := hx; exact hloc j
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, mul_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, mul_left_comm]
      exact mul_mem (SelfDual.inclR_mem_intLoc v ⟨r, rfl⟩) hx
  have key : ∀ z ∈ I * J, Valued.v (toCompl hw (c * inclR (Fv F v) z)) ≤
      WithZero.exp (-FractionalIdeal.count E w I) := by
    intro z hz
    refine FractionalIdeal.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have h2 : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
      rw [map_mul (inclR (Fv F v)) x y, mul_left_comm, map_mul, toCompl_inclR, map_mul, h2]
      exact (mul_le_mul' (GlobalTheory.UnrTate.valuation_le_of_mem w hx)
        (valued_toCompl_le_one hw (hJloc y hy))).trans_eq (mul_one _)
    · rw [map_add, mul_add, map_add]
      exact Valuation.map_add_le _ hx hy
  have := key 1 h1IJ
  rw [map_one, mul_one] at this
  rwa [GlobalTheory.UnrTate.valAt_of_under hw]

end GlobalTheory.LineLocVal
