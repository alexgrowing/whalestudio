import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem oneVar {F : Type} [Field F] [NumberField F] (f w : A F → ℝ≥0∞) (hf : Measurable f) (hw : Measurable w)
    (hinv : ∀ (ξ : F) b, f (rt ξ + b) = f b) (hsum : ∀ b, ∑' ξ : F, w (rt ξ + b) = 1) :
    ∫⁻ b, f b * w b ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, f b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  let φ : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := hφ.2.countable
  rw [hD.lintegral_eq_tsum'' (fun b => f b * w b), ← lintegral_tsum]
  · refine lintegral_congr fun x => ?_
    rw [← (Equiv.ofBijective φ hφ).tsum_eq]
    have h1 : ∀ ξ : F, f ((Equiv.ofBijective φ hφ ξ) +ᵥ x) * w ((Equiv.ofBijective φ hφ ξ) +ᵥ x) = f x * w (rt ξ + x) := by
      intro ξ
      change f (rt ξ + x) * w (rt ξ + x) = _
      rw [hinv]
    simp only [h1]
    rw [ENNReal.tsum_mul_left, hsum, mul_one]
  · intro γ
    exact ((hf.mul hw).comp (measurable_const_add (γ : A F))).aemeasurable

theorem UpperTheory.ConvolutionTheory.R2.M.wtInt :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞), M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ β u hβ hu hinv
  haveI := M₀.prob
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  have hmD : Measurable (mD : IdeleGroup F → G1 F) := M.continuous_mD.measurable
  have hy : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    (hmD.comp measurable_fst).mul measurable_snd
  have hI : Measurable fun p : IdeleGroup F × G1 F =>
      ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : (IdeleGroup F × G1 F) × A F => u (nU q.2 * (mD q.1.1 * q.1.2)))
      (hu.comp ((hnU.comp measurable_snd).mul (hy.comp measurable_fst)))
  have hJ : Measurable fun p : IdeleGroup F × G1 F =>
      M.wt p.1 * ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    (M.measurable_wt.comp measurable_fst).mul hI
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ.1), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable]
  refine lintegral_congr fun k => lintegral_congr fun a => ?_
  have hsh : ∀ (ξ : F) (b : A F) (y : G1 F), nU (rt ξ + b) * y = nU (rt ξ) * (nU b * y) := by
    intro ξ b y
    rw [M.nU_add, mul_assoc]
  have hmy : ∀ v : G1 F → ℝ≥0∞, Measurable v → Measurable fun b : A F => v (nU b * (mD a * k)) :=
    fun v hv => hv.comp (hnU.mul_const _)
  have key := oneVar (fun b => u (nU b * (mD a * k))) (fun b => β (nU b * (mD a * k)))
    (hmy u hu) (hmy β hβ.1) (fun ξ b => by simp only [hsh, hinv])
    (fun b => by simp only [hsh]; exact hβ.2 _)
  simp only [mul_assoc (nU _) (mD a) k]
  rw [lintegral_mul_const (f := fun b => u (nU b * (mD a * k)) * β (nU b * (mD a * k))) _
    ((hmy u hu).mul (hmy β hβ.1)), key, mul_comm]
  rfl
