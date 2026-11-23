import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem pair_abs {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [SFinite ν] (k : X → Y → ℂ) (e : X → X → ℂ)
    (hk : Measurable (Function.uncurry k)) (he : Measurable (Function.uncurry e))
    (hkn : ∀ v y, ‖k v y‖ = 1) (hen : ∀ v z, ‖e v z‖ = 1)
    (φ : Y → ℂ) (hφ : Integrable φ ν) (hJ : Integrable (fun v => ∫ y, φ y * k v y ∂ν) μ)
    (Φ : X → ℂ) (hΦ : Integrable Φ μ) (H : X → ℂ) (hHi : Integrable H μ)
    (hH : ∀ v, H v = ∫ z, Φ z * e v z ∂μ) (hinv : ∀ y, ∫ v, H v * k v y ∂μ = 0) :
    ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ = 0 := by
  have h1 : Integrable (Function.uncurry fun (z v : X) =>
      (∫ y, φ y * k v y ∂ν) * e v z * Φ z) (μ.prod μ) := by
    refine Integrable.mono (hΦ.mul_prod hJ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × X => ∫ y, φ y * k p.2 y ∂ν) (μ.prod μ) :=
        hJ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × X => e p.2 p.1) (μ.prod μ) :=
        (he.comp measurable_swap).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × X => Φ p.1) (μ.prod μ) :=
        hΦ.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨z, v⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hen, mul_one]
      exact le_of_eq (mul_comm _ _)
  have h2 : Integrable (Function.uncurry fun (v : X) (y : Y) => φ y * k v y * H v) (μ.prod ν) := by
    refine Integrable.mono (hHi.mul_prod hφ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × Y => φ p.2) (μ.prod ν) :=
        hφ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × Y => k p.1 p.2) (μ.prod ν) :=
        hk.aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × Y => H p.1) (μ.prod ν) :=
        hHi.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨v, y⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hkn, mul_one]
      exact le_of_eq (mul_comm _ _)
  calc ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ
      = ∫ z, ∫ v, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := by
        congr 1; funext z
        exact (integral_mul_const (Φ z) _).symm
    _ = ∫ v, ∫ z, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := integral_integral_swap h1
    _ = ∫ v, (∫ y, φ y * k v y ∂ν) * H v ∂μ := by
        congr 1; funext v
        rw [hH v, ← integral_const_mul]
        congr 1; funext z; ring
    _ = ∫ v, ∫ y, φ y * k v y * H v ∂ν ∂μ := by
        congr 1; funext v
        exact (integral_mul_const (H v) _).symm
    _ = ∫ y, ∫ v, φ y * k v y * H v ∂μ ∂ν := integral_integral_swap h2
    _ = ∫ y, φ y * ∫ v, H v * k v y ∂μ ∂ν := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext v; ring
    _ = 0 := by simp [hinv]

theorem haar_facts {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] :
    SFinite μ ∧ μ.IsNegInvariant :=
  ⟨inferInstance, inferInstance⟩

theorem pair_ring {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (μ : Measure (κ → R)) [SFinite μ]
    [μ.IsNegInvariant] (ψ : AddChar R ℂ) (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → R)
    (hφ : Integrable φ ν) (hg : Measurable g)
    (hJ : Integrable (fun v : κ → R => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ)
    (Φ : (κ → R) → ℂ) (hΦi : Integrable Φ μ)
    (hHi : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ)
    (hinv : ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x))
    (h0 : ∀ y, Φ (g y) = 0) :
    ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → R) × (κ → R) => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  have hk : Measurable (Function.uncurry fun (v : κ → R) (y : Y) => ψ (v ⬝ᵥ g y)) := by
    have hm : Measurable (fun p : (κ → R) × (κ → R) => ψ (p.1 ⬝ᵥ p.2)) :=
      (hc.comp hdot).measurable
    exact hm.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  have he : Measurable (Function.uncurry fun (v z : κ → R) => ψ (-(v ⬝ᵥ z))) :=
    (hc.comp hdot.neg).measurable
  have hHi' : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (-(w ⬝ᵥ z)) ∂μ) μ := by
    refine hHi.comp_neg.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [dotProduct_neg]
    congr 1; funext z
    rw [dotProduct_comm]
  have hinv' : ∀ y, ∫ v, (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y) ∂μ = 0 := by
    intro y
    have h1 := hinv (-(g y))
    rw [neg_neg, h0 y] at h1
    refine (integral_neg_eq_self
      (fun v => (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y)) μ).symm.trans (Eq.trans ?_ h1)
    congr 1; funext v
    simp only [neg_dotProduct, neg_neg, dotProduct_neg]
    congr 1; congr 1; funext z
    rw [dotProduct_comm]
  exact pair_abs μ ν (fun v y => ψ (v ⬝ᵥ g y)) (fun v z => ψ (-(v ⬝ᵥ z))) hk he
    (fun v y => hn _) (fun v z => hn _) φ hφ hJ Φ hΦi _ hHi' (fun v => rfl) hinv'

theorem pair_vanish : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Y _ ν _ φ g hφ hg hJ Φ hΦ h0
  have hH : μ.IsAddHaarMeasure := hμ.1
  obtain ⟨hS, hN⟩ := haar_facts μ
  have hc : Continuous ψ := hψ.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  obtain ⟨-, -, hint⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  have hinv := GlobalTheory.TamFourier.fourier_inversion_tamagawa F hF ψ hψ κ μ hμ Φ hΦ
  have hHi : Integrable (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ := by
    by_contra hni
    have hzero : ∀ x, Φ x = 0 := by
      intro x
      have h1 := hinv (-x)
      rw [neg_neg] at h1
      rw [← h1]
      apply integral_undef
      intro hi
      apply hni
      exact integrable_of_mul_unimodular μ (fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ)
        (fun y => ψ (y ⬝ᵥ -x)) hi
        ((hc.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable) (fun y => hn _)
    apply hni
    have hfun : (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) = fun _ => (0 : ℂ) := by
      funext w; simp [hzero]
    rw [hfun]
    exact integrable_zero _ _ _
  exact pair_ring μ ψ hc hn ν φ g hφ hg hJ Φ (hint μ hH) hHi hinv h0

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
