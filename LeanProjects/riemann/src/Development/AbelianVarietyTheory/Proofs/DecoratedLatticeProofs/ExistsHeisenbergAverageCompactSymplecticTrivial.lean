import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisAvgCompact

theorem exists_average_of_compact {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (K : AddSubgroup X) (hK : IsCompact (K : Set X)) (f : X → X → ℂ)
    (hf : Continuous fun p : X × X => f p.1 p.2) :
    ∃ g : X → ℂ, Continuous g ∧
      (∀ (c : ℂ) (x y : X), (∀ u ∈ K, f x u = c * f y u) → g x = c * g y) ∧
      (∀ (c : ℂ) (x y : X), ∀ u₀ ∈ K, (∀ u ∈ K, c * f x u = f y (u₀ + u)) → c * g x = g y) ∧
      ∀ (δ : ℝ) (z : ℂ) (w : X), (∀ a ∈ K, ‖f w a - z‖ ≤ δ) → ‖g w - z‖ ≤ δ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  letI mK : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := Measure.addHaarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have h := Measure.addHaarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h⟩
  have hF : Continuous (Function.uncurry fun (w : X) (u : K) => f w u) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfw : ∀ w, Continuous fun u : K => f w u := fun w => hF.comp (Continuous.prodMk_right w)
  have hint : ∀ w, Integrable (fun u : K => f w u) ν := fun w =>
    integrableOn_univ.1 ((hfw w).continuousOn.integrableOn_compact isCompact_univ)
  refine ⟨fun w => ∫ u : K, f w u ∂ν, ?_, ?_, ?_, ?_⟩
  · have h := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using h
  · intro c x y h
    show (∫ u : K, f x u ∂ν) = c * ∫ u : K, f y u ∂ν
    rw [← integral_const_mul]
    congr 1
    funext u
    exact h u u.2
  · intro c x y u₀ hu₀ h
    show c * (∫ u : K, f x u ∂ν) = ∫ u : K, f y u ∂ν
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun u : K => f y u) (⟨u₀, hu₀⟩ : K)]
    congr 1
    funext u
    exact h u u.2
  · intro δ z w hδ
    have hc : (∫ _u : K, z ∂ν) = z := by
      rw [integral_const, probReal_univ, one_smul]
    show ‖(∫ u : K, f w u ∂ν) - z‖ ≤ δ
    rw [← hc, ← integral_sub (hint w) (integrable_const _)]
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := δ) (f := fun u : K => f w u - z)
      (Filter.Eventually.of_forall fun u : K => hδ u u.2)
    rwa [probReal_univ, mul_one] at h

theorem exists_average : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (K : AddSubgroup (WO A T)), IsCompact (K : Set (WO A T)) → (∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1) → ∀ (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∃ g : WO A T → ℂ, Continuous g ∧ (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), g (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * g u) ∧ (∀ u ∈ K, heisO ψ A T u g = g) ∧ ∀ δ : ℝ, (∀ a ∈ K, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ δ) → ∀ w, ‖g w - q w‖ ≤ δ := by
  intro D ψ hψ A T K hK hKψ q hq hquasi
  obtain ⟨hTG, hLC, hSC, hT2, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
  have hψc : Continuous ψ := hψ.1.1
  have hadd : Continuous fun p : WO A T × WO A T => p.1 + p.2 := hTG.toContinuousAdd.continuous_add
  have hf : Continuous fun p : WO A T × WO A T => heisO ψ A T p.2 q p.1 :=
    (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)).mul (hq.comp hadd)
  obtain ⟨g, h1, h2, h3, h4⟩ := @exists_average_of_compact (WO A T) _ _ hTG hLC hSC hT2 K hK
    (fun w u => heisO ψ A T u q w) hf
  refine ⟨g, h1, fun γ w => h2 _ _ _ fun u _ => GlobalTheory.OrientedHeis.heisO_quasi u q hquasi γ w,
    fun u₀ hu₀ => funext fun w => h3 (ψ (symplOH A T w u₀)) (w + u₀) w u₀ hu₀ fun u hu => ?_,
    fun δ hδ w => h4 δ (q w) w fun a ha => hδ a ha w⟩
  have h := congrFun (GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) u₀ u q) w
  rw [hKψ u₀ hu₀ u hu, one_smul] at h
  exact h

end GlobalTheory.HeisAvgCompact
