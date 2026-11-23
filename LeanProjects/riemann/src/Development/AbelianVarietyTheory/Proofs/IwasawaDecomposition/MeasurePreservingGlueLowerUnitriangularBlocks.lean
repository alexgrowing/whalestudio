import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecOfMulToMatMul

noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

def lowPos {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : (Fin p × Fin q) ⊕ Low q ⊕ Low p → Low r
  | .inl s => ⟨(e.symm (.inl s.1), e.symm (.inr s.2)), by
      rw [Fin.lt_def]; simp only [he.1, he.2]; have := s.2.2; omega⟩
  | .inr (.inl s) => ⟨(e.symm (.inr s.1.1), e.symm (.inr s.1.2)), by
      rw [Fin.lt_def]; simp only [he.2]; exact s.2⟩
  | .inr (.inr s) => ⟨(e.symm (.inl s.1.1), e.symm (.inl s.1.2)), by
      rw [Fin.lt_def]; simp only [he.1]; have : (s.1.2 : ℕ) < s.1.1 := s.2; omega⟩

theorem lowPos_bijective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Bijective (lowPos he) := by
  constructor
  · rintro (⟨a, b⟩ | ⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) (⟨c, d⟩ | ⟨⟨c, d⟩, h'⟩ | ⟨⟨c, d⟩, h'⟩) hx <;>
      simp_all [lowPos]
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    obtain ⟨b, rfl⟩ := e.symm.surjective b
    have h : (e.symm b : ℕ) < e.symm a := hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at h
    · exact ⟨.inr (.inr ⟨(a, b), by rw [Fin.lt_def]; simp only; omega⟩), rfl⟩
    · exact ⟨.inl (a, b), rfl⟩
    · have := a.2; omega
    · exact ⟨.inr (.inl ⟨(a, b), h⟩), rfl⟩

theorem measurePreserving_mul_uni (y : Low q → ℂ) :
    MeasurePreserving (fun v : Fin p × Fin q → ℂ => vecOf (toMat v * uni y)) volume volume := by
  have hc : Continuous fun v : Fin p × Fin q → ℂ => vecOf (toMat v * uni y) :=
    continuous_pi fun s => (continuous_toMat.matrix_mul continuous_const).matrix_elem s.1 s.2
  refine ⟨hc.measurable, Measure.ext fun s hs => ?_⟩
  have h := GlobalTheory.FlagFibre.lintegral_affine p q 1 (uni y) 0 (by simp) (by simp [det_uni]) (s.indicator 1)
    (measurable_one.indicator hs)
  simp only [Matrix.one_mul, add_zero, det_uni, det_one, map_one, one_pow, mul_one, inv_one,
    ENNReal.ofReal_one, one_mul] at h
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hc.measurable, h]

theorem measurePreserving_shear_uni :
    MeasurePreserving (fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) =>
      (vecOf (toMat w.1 * uni w.2.1), w.2)) volume volume := by
  have hc : Continuous (Function.uncurry fun (y : (Low q → ℂ) × (Low p → ℂ)) (v : Fin p × Fin q → ℂ) =>
      vecOf (toMat v * uni y.1)) :=
    continuous_pi fun s => ((continuous_toMat.comp continuous_snd).matrix_mul
      (continuous_uni.comp (continuous_fst.comp continuous_fst))).matrix_elem s.1 s.2
  have h := (MeasurePreserving.id (volume : Measure ((Low q → ℂ) × (Low p → ℂ)))).skew_product
    (μc := volume) (μd := volume) hc.measurable
    (Filter.Eventually.of_forall fun y => (measurePreserving_mul_uni y.1).map_eq)
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem measurePreserving_glue (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q) (he : IsBlockSL2Embedding e) :
    MeasurePreserving (glue e) volume volume := by
  let σ := Equiv.ofBijective _ (lowPos_bijective he)
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Low r => ℂ) σ
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin p × Fin q) ⊕ Low q ⊕ Low p => ℂ)
  have h3 := (MeasurePreserving.id (volume : Measure (Fin p × Fin q → ℂ))).prod
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Low q ⊕ Low p => ℂ))
  have h := h1.comp (h2.comp (h3.comp measurePreserving_shear_uni))
  convert h using 1
  funext w s
  obtain ⟨x, rfl⟩ := σ.surjective s
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rcases x with ⟨a, b⟩ | ⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩
  · simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₁₂]
    rfl
  · have hab' : b < a := hab
    simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₂₂, uni,
      of_apply, dif_pos hab']
    rfl
  · have hab' : b < a := hab
    simp only [σ, Equiv.ofBijective_apply, lowPos, glue, Equiv.apply_symm_apply, fromBlocks_apply₁₁, uni,
      of_apply, dif_pos hab']
    rfl

end GlobalTheory.FlagFibre
