import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem pi_map_update_add {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {n : ℕ}
    (ν : Measure V) [SigmaFinite ν] [ν.IsAddRightInvariant] (a : Fin n) (T : (Fin n → V) → V)
    (hT : Measurable T) (hTa : ∀ x y, T (Function.update x a y) = T x) :
    (Measure.pi fun _ : Fin n => ν).map (fun x => Function.update x a (x a + T x)) =
      Measure.pi fun _ : Fin n => ν := by
  have hf : Measurable (fun x : Fin n → V => Function.update x a (x a + T x)) := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases h : j = a
    · subst h
      simp only [Function.update_self]
      exact (measurable_pi_apply j).add hT
    · simpa [Function.update_of_ne h] using measurable_pi_apply j
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [← Measure.pi_pi, ← lintegral_indicator_one h2s, ← lintegral_indicator_one h2s,
    lintegral_map (measurable_one.indicator h2s) hf]
  refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp hf)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have key : ∀ y : V, Function.update (Function.update x a y) a (Function.update x a y a + T (Function.update x a y))
      = Function.update x a (y + T x) := by
    intro y
    simp [hTa]
  simp only [Function.comp_def, key]
  exact lintegral_add_right_eq_self
    (fun y => (Set.univ.pi s).indicator (1 : (Fin n → V) → ℝ≥0∞) (Function.update x a y)) (T x)

theorem coordW_map_shearK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam a s hs
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) := inferInstance
  haveI hν : (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).IsAddHaarMeasure := inferInstance
  have hmul : ∀ c : Ainf F ⊗[F] E, Measurable (fun y : Ainf F ⊗[F] E => c * y) := fun c =>
    (continuous_const.mul continuous_id).measurable
  have hT : Measurable (fun (x : Fin n → Fin M → Ainf F ⊗[F] E) (i : Fin M) => ∑ c, s c * x c i) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (hmul (s c)).comp ((measurable_pi_apply i).comp (measurable_pi_apply c))
  have hTa : ∀ (x : Fin n → Fin M → Ainf F ⊗[F] E) (y : Fin M → Ainf F ⊗[F] E),
      (fun i => ∑ c, s c * Function.update x a y c i) = fun i => ∑ c, s c * x c i := by
    intro x y
    funext i
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = a
    · subst h; simp [hs]
    · simp [Function.update_of_ne h]
  exact pi_map_update_add (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) a _ hT hTa

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
