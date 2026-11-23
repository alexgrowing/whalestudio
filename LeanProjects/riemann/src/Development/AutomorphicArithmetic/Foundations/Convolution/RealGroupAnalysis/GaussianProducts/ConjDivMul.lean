import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomAdel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExpInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Factor
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EqNUMul
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AeZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem row_mD {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (g : G1 F) :
    UpperTheory.ConvolutionTheory.R2.G.row (mD a * g) = fun j => ((a⁻¹ : (A F)ˣ) : A F) * g 1 j := by
  funext j
  change ((mD a).1 * g.1) 1 j = _
  simp [mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cont_row {F : Type} [Field F] [NumberField F] :
    Continuous (fun p : IdeleGroup F × G1 F => UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) := by
  have e : (fun p : IdeleGroup F × G1 F => UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) =
      fun p j => (((p.1 : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) * p.2 1 j := by
    funext p
    exact row_mD _ _
  rw [e]
  refine continuous_pi fun j => ?_
  have h1 : Continuous fun p : IdeleGroup F × G1 F => (((p.1 : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) :=
    Units.continuous_val.comp (continuous_inv.comp continuous_fst)
  have h2 : Continuous fun g : G1 F => g 1 j :=
    (continuous_apply j).comp ((continuous_apply (1 : Fin 2)).comp
      (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous))
  exact h1.mul (h2.comp continuous_snd)

private theorem conj_div_mul (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    (starRingEnd ℂ z) / (‖z‖ : ℂ) * ((c : ℂ) * z) = ((‖(c : ℂ) * z‖ : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
  have h1 : starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := Complex.conj_mul' z
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  push_cast
  field_simp
  linear_combination (c : ℂ) * h1

private theorem ae_KK {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) :
    ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
  rw [ae_iff]
  have e : {p : IdeleGroup F × G1 F | ¬ p.2 ∈ KK F} = Set.univ ×ˢ (KK F)ᶜ := by
    ext p
    simp
  haveI := M.prob
  rw [e, Meas.ν, Measure.prod_prod, M.supp, mul_zero]

private theorem exists_q {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (u : G1 F → ℂ)
    (hc : ContinuousOn (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) (Set.univ ×ˢ KK F))
    (hrow : ∀ g g', UpperTheory.ConvolutionTheory.R2.G.row g = UpperTheory.ConvolutionTheory.R2.G.row g' → u g = u g') :
    ∃ h : (Fin 2 → A F) → ℂ, Measurable h ∧ ∀ (a : IdeleGroup F), ∀ k ∈ KK F,
      h (UpperTheory.ConvolutionTheory.R2.G.row (mD a * k)) = u (mD a * k) := by
  have hr := cont_row (F := F)
  haveI : CompactSpace (KK F) := isCompact_iff_compactSpace.1 (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
  have hι : Continuous fun x : IdeleGroup F × KK F => ((x.1, x.2.1) : IdeleGroup F × G1 F) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmem : ∀ x : IdeleGroup F × KK F,
      ((x.1, x.2.1) : IdeleGroup F × G1 F) ∈ (Set.univ ×ˢ KK F : Set (IdeleGroup F × G1 F)) :=
    fun x => Set.mk_mem_prod (Set.mem_univ _) x.2.2
  have hH : Continuous fun x : IdeleGroup F × KK F => u (mD x.1 * x.2.1) := by
    have h := ContinuousOn.comp_continuous (g := fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2))
      (f := fun x : IdeleGroup F × KK F => ((x.1, x.2.1) : IdeleGroup F × G1 F)) hc hι hmem
    simpa only [Function.comp_def] using h
  have hR : Continuous fun x : IdeleGroup F × KK F => UpperTheory.ConvolutionTheory.R2.G.row (mD x.1 * x.2.1) := by
    have h := hr.comp hι
    simpa only [Function.comp_def] using h
  obtain ⟨h, hm, hh⟩ := UpperTheory.ConvolutionTheory.R2.G.factor (IdeleGroup F × KK F) (Fin 2 → A F)
    (fun x => UpperTheory.ConvolutionTheory.R2.G.row (mD x.1 * x.2.1)) (fun x => u (mD x.1 * x.2.1))
    hR hH (fun x x' e => hrow _ _ e)
  exact ⟨h, hm, fun a k hk => hh (a, ⟨k, hk⟩)⟩

private theorem core {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F)
    (u : G1 F → ℂ)
    (hc : ContinuousOn (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) (Set.univ ×ˢ KK F))
    (hrow : ∀ g g', UpperTheory.ConvolutionTheory.R2.G.row g = UpperTheory.ConvolutionTheory.R2.G.row g' → u g = u g')
    (hI : Integrable (iw u) M.ν)
    (hmom : ∀ q : (Fin 2 → A F) → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) →
      ∫ p : IdeleGroup F × G1 F, q (UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) * iw u p ∂M.ν = 0) :
    ∀ a, ∀ k ∈ KK F, u (mD a * k) = 0 := by
  obtain ⟨h, hm, hh⟩ := exists_q u hc hrow
  let q : (Fin 2 → A F) → ℂ := fun y => (starRingEnd ℂ (h y)) / (‖h y‖ : ℂ)
  have hqm : Measurable q :=
    (Complex.continuous_conj.measurable.comp hm).div (Complex.continuous_ofReal.measurable.comp hm.norm)
  have hq1 : ∀ y, ‖q y‖ ≤ 1 := by
    intro y
    by_cases e : h y = 0
    · simp [q, e]
    · have hn : ‖h y‖ ≠ 0 := by simpa using e
      simp [q, hn]
  have hae : (fun p : IdeleGroup F × G1 F => q (UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) * iw u p) =ᵐ[M.ν]
      fun p => ((‖iw u p‖ : ℝ) : ℂ) := by
    filter_upwards [ae_KK M] with p hp
    have e' : h (UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2)) = u (mD p.1 * p.2) := hh p.1 p.2 hp
    simp only [q, e', iw]
    exact conj_div_mul _ (by positivity) _
  have hz : ∫ p, ‖iw u p‖ ∂M.ν = 0 := by
    have h1 : ∫ p, ((‖iw u p‖ : ℝ) : ℂ) ∂M.ν = 0 := by
      rw [← integral_congr_ae hae]
      exact hmom q hqm hq1
    rw [integral_complex_ofReal] at h1
    exact_mod_cast h1
  have hz' := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hI.norm).1 hz
  refine UpperTheory.ConvolutionTheory.R2.G.aeZero F M (fun p => u (mD p.1 * p.2)) hc ?_
  filter_upwards [hz'] with p hp
  have hp' : iw u p = 0 := by simpa using hp
  have hpos : 0 < ab (p.1 : (A F)ˣ) := (IdeleGroup.ideleModule F p.1).2
  have hne : ((((ab p.1)⁻¹ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    have : ((ab p.1)⁻¹ ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  exact (mul_eq_zero.1 hp').resolve_left hne

theorem UpperTheory.ConvolutionTheory.R2.G.zeroW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, (∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0) → ∀ φ ∈ Fock D.δ, ∀ a, ∀ k ∈ KK F, w1 W f.1 φ 1 (mD a * k) = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf h0 φ hφ
  obtain ⟨hc, hrow⟩ := UpperTheory.ConvolutionTheory.R2.G.contW F E D W M π f hf φ hφ
  have hE := UpperTheory.ConvolutionTheory.R2.G.expInt F E D W M π f hf φ hφ
  have hI : Integrable (iw (w1 W f.1 φ 1)) M.ν := by
    simpa using hE 0
  exact core M _ hc hrow hI fun q hq hq1 =>
    UpperTheory.ConvolutionTheory.R2.G.momAdel F (IdeleGroup F × G1 F) M.ν (fun p => UpperTheory.ConvolutionTheory.R2.G.row (mD p.1 * p.2))
      (iw (w1 W f.1 φ 1)) cont_row.measurable hE
      (UpperTheory.ConvolutionTheory.R2.G.momZero F E D W M π f hf h0 φ hφ) q hq hq1
