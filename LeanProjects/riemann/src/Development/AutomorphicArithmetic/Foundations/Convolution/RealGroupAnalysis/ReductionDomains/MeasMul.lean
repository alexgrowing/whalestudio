import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.SumSide
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IwDens

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem absUnf {G P B ι : Type} [MeasurableSpace G] [MeasurableSpace P] [MeasurableSpace B] [Countable ι]
    (m₀ : Measure G) (e : ι → G → G) (he : ∀ i, Measurable (e i)) (ρ : Measure P) [SFinite ρ]
    (β : Measure B) [SFinite β] (s : P × B → G) (hs : Measurable s) (u : G → ℂ) (hu : Measurable u)
    (hL : ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      ∫⁻ x, ∑' i, φ (u (e i x)) ∂m₀ = ∫⁻ q, φ (u (s q)) ∂(ρ.prod β))
    (hfin : ∫⁻ q, ‖u (s q)‖ₑ ∂(ρ.prod β) ≠ ⊤) :
    (∀ᵐ x ∂m₀, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m₀ ∧
      Integrable (fun p => ∫ b, u (s (p, b)) ∂β) ρ ∧
      ∫ x, ∑' i, u (e i x) ∂m₀ = ∫ p, ∫ b, u (s (p, b)) ∂β ∂ρ := by
  have hS := M.sumSide G ι m₀ e he
  have hv : Measurable fun q => u (s q) := hu.comp hs
  have hvi : Integrable (fun q => u (s q)) (ρ.prod β) :=
    ⟨hv.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hT := M.transfer (m := Measure.sum fun i => m₀.map (e i)) (n := ρ.prod β) hu hv
    (fun φ hφ => (hS.1 _ (hφ.comp hu)).trans (hL φ hφ))
  obtain ⟨h1, h2, h3⟩ := hS.2 u hu (hT.1.2 hvi)
  refine ⟨h1, h2, hvi.integral_prod_left, h3.trans (hT.2.trans ?_)⟩
  exact integral_prod _ hvi

private theorem meas_mul (F : Type) [Field F] [NumberField F] : Measurable fun q : G1 F × G1 F => q.1 * q.2 :=
  (continuous_fst.mul continuous_snd).measurable

private theorem meas_nU (F : Type) [Field F] [NumberField F] : Measurable (nU : A F → G1 F) :=
  M.continuous_nU.measurable

private theorem meas_mD (F : Type) [Field F] [NumberField F] : Measurable (mD : IdeleGroup F → G1 F) :=
  M.continuous_mD.measurable

private theorem measMul {G X : Type} [Mul G] [MeasurableSpace G] [MeasurableSpace X] {a b : X → G}
    (hm : Measurable fun q : G × G => q.1 * q.2) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => a x * b x := hm.comp (ha.prodMk hb)

private theorem meas_g (F : Type) [Field F] [NumberField F] :
    Measurable fun q : G1 F × A F => nU q.2 * q.1 :=
  measMul (a := fun q : G1 F × A F => nU q.2) (b := fun q => q.1) (meas_mul F)
    ((meas_nU F).comp measurable_snd) measurable_fst

private theorem meas_m (F : Type) [Field F] [NumberField F] :
    Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
  measMul (a := fun p : IdeleGroup F × G1 F => mD p.1) (b := fun p => p.2) (meas_mul F)
    ((meas_mD F).comp measurable_fst) measurable_snd

private theorem meas_q (F : Type) [Field F] [NumberField F] :
    Measurable fun q : (IdeleGroup F × G1 F) × A F => nU q.2 * (mD q.1.1 * q.1.2) :=
  measMul (a := fun q : (IdeleGroup F × G1 F) × A F => nU q.2)
    (b := fun q => mD q.1.1 * q.1.2) (meas_mul F)
    ((meas_nU F).comp measurable_snd) ((meas_m F).comp measurable_fst)

private theorem meas_l (F : Type) [Field F] [NumberField F] (x : G1 F) :
    Measurable fun g : G1 F => x * g :=
  measMul (a := fun _ : G1 F => x) (b := fun g => g) (meas_mul F) measurable_const measurable_id

private theorem key (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (ρ : Measure (IdeleGroup F × G1 F)) [SFinite ρ]
    (hρ : ∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u)
    (w : G1 F → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ q, w (nU q.2 * (mD q.1.1 * q.1.2)) ∂(ρ.prod ((adeleMeasure F).restrict (fundamentalSet F))) =
      M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, w (nU b * g) ∂(adeleMeasure F) := by
  refine (lintegral_prod (fun q : (IdeleGroup F × G1 F) × A F => w (nU q.2 * (mD q.1.1 * q.1.2)))
    (hw.comp (meas_q F)).aemeasurable).trans ?_
  exact hρ _ (Measurable.lintegral_prod_right' (f := fun q : G1 F × A F => w (nU q.2 * q.1)) (hw.comp (meas_g F)))

theorem UpperTheory.ConvolutionTheory.R2.M.unfC :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (u : G1 F → ℂ), M.RowSec (F := F) σ → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → (M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F)) ≠ ⊤ → (∀ᵐ g ∂(M₀.μ.restrict M₀.D), Summable fun r => ‖u (ratS F (σ r) * g)‖) ∧ IntegrableOn (fun g => ∑' r, u (ratS F (σ r) * g)) M₀.D M₀.μ ∧ Integrable (iw fun g => ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F)) M₀.ν ∧ ∫ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ = M₀.I0 fun g => ∫ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ σ u hσ hu hinv hfin
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨ρ, hρs, hρ1, hρ2⟩ := M.iwDens F M₀
  have hk := key F M₀ ρ hρ1
  obtain ⟨h1, h2, h3, h4⟩ := absUnf (M₀.μ.restrict M₀.D) (fun (r : {r : Fin 2 → F // r ≠ 0}) g => ratS F (σ r) * g)
    (fun r => meas_l F _) ρ ((adeleMeasure F).restrict (fundamentalSet F))
    (fun q => nU q.2 * (mD q.1.1 * q.1.2)) (meas_q F) u hu
    (fun φ hφ => (M.unfL F M₀ σ (fun g => φ (u g)) hσ (hφ.comp hu)
        (fun ξ g => by simp only [hinv])).trans (hk _ (hφ.comp hu)).symm)
    (by rw [hk (fun g => ‖u g‖ₑ) hu.enorm]; exact hfin)
  refine ⟨h1, h2, ((hρ2 _).1).1 h3, h4.trans ((hρ2 _).2)⟩
