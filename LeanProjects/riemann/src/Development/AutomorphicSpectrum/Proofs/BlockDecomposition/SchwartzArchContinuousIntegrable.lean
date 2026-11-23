import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple

theorem decay_of_functionals {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [Fintype ι] {N : ℕ}
    (e : V ≃+ (Fin N → ℝ)) (hes : Continuous e.symm) (c : ι → V →+ ℂ) (hc : ∀ i, Continuous (c i))
    (f : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X : V, (∃ i, R < ‖c i X‖) → ‖f (e X)‖ ≤ C / R ^ k := by
  let L : ι → (Fin N → ℝ) →L[ℝ] ℂ := fun i =>
    ((c i).comp e.symm.toAddMonoidHom).toRealLinearMap ((hc i).comp hes)
  have hL : ∀ i X, c i X = L i (e X) := by
    intro i X
    show c i X = c i (e.symm (e X))
    rw [e.symm_apply_apply]
  set T : ℝ := ∑ i, ‖L i‖ + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ ∑ i, ‖L i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨C0, hC0⟩ := f.decay k 0
  refine ⟨C0 * T ^ k, fun R hR X ⟨i, hi⟩ => ?_⟩
  have hRpos : 0 < R := by linarith
  set x := e X with hx
  have hb : ‖c i X‖ ≤ T * ‖x‖ := by
    rw [hL]
    refine ((L i).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have : ‖L i‖ ≤ ∑ j, ‖L j‖ :=
      Finset.single_le_sum (f := fun j => ‖L j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  have hRx : R ≤ T * ‖x‖ := hi.le.trans hb
  have hd : ‖x‖ ^ k * ‖f x‖ ≤ C0 := by
    simpa [norm_iteratedFDeriv_zero] using hC0.2 x
  rw [le_div_iff₀ (pow_pos hRpos k)]
  calc ‖f x‖ * R ^ k ≤ ‖f x‖ * (T * ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRpos.le hRx k) (norm_nonneg _)
    _ = (‖x‖ ^ k * ‖f x‖) * T ^ k := by rw [mul_pow]; ring
    _ ≤ C0 * T ^ k := mul_le_mul_of_nonneg_right hd (pow_nonneg hTpos.le k)

theorem schwartzArch_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)), IsHomeomorph κ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Continuous φ ∧ Integrable φ (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) ∧ (∃ B : ℝ, ∀ X, ‖φ X‖ ≤ B) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k := by
  intro F E _ _ _ _ _ σ hCM κ hκ n M d b lam hlam φ hφ
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, hsc, -, hrepr, hB, -, hgc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hB n M
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b lam hlam
  haveI := hW n M
  obtain ⟨N, e, he, hes, f, hf⟩ := hφ
  have hφe : φ = fun x => f (e x) := funext hf
  have hφc : Continuous φ := by rw [hφe]; exact f.continuous.comp he
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμ
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hint : Integrable φ μ := by
    have h1 : Integrable (fun x => f x) (μ.map e) := f.integrable
    rw [hφe]
    exact (integrable_map_measure h1.aestronglyMeasurable he.measurable.aemeasurable).1 h1
  refine ⟨hφc, hint, ?_, fun k => ?_⟩
  · obtain ⟨C0, hC0⟩ := f.decay 0 0
    refine ⟨C0, fun X => ?_⟩
    rw [hf]
    simpa [norm_iteratedFDeriv_zero] using hC0.2 (e X)
  · let c : (Fin n × Fin M × NumberField.InfinitePlace F) → (Fin n → Fin M → Ainf F ⊗[F] E) →+ ℂ := fun p =>
      { toFun := fun X => κ (X p.1 p.2.1) p.2.2
        map_zero' := by simp
        map_add' := fun X Y => by simp }
    have hc : ∀ p, Continuous (c p) := fun p =>
      (continuous_apply p.2.2).comp (hκ.continuous.comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1)))
    obtain ⟨C, hC⟩ := decay_of_functionals e hes c hc f k
    refine ⟨C, fun R hR X hX => ?_⟩
    rw [hf]
    refine hC R hR X ?_
    simp only [boxK, Set.mem_setOf_eq, not_forall, not_le] at hX
    obtain ⟨a, i, w, h⟩ := hX
    exact ⟨(a, i, w), h⟩

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple
