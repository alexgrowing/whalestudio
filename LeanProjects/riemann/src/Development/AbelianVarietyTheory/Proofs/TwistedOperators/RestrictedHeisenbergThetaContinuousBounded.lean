import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_bounded_setIntegral {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) (F : X → Y → ℂ)
    (hc : Continuous fun q : X × Y => F q.1 q.2) (K : ℝ) (hb : ∀ x y, ‖F x y‖ ≤ K) :
    Continuous (fun x => ∫ y in s, F x y ∂μ) ∧ ∀ x, ‖∫ y in s, F x y ∂μ‖ ≤ K * (μ.restrict s).real Set.univ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  refine ⟨?_, fun x => norm_integral_le_of_norm_le_const (.of_forall fun y => hb x y)⟩
  refine continuous_of_dominated (bound := fun _ => K) (fun x => ?_) (fun x => .of_forall fun y => hb x y)
    (integrable_const K) (.of_forall fun y => ?_)
  · exact (hc.comp (continuous_const.prodMk continuous_id) : Continuous fun y => F x y).aestronglyMeasurable
  · exact (hc.comp (continuous_id.prodMk continuous_const) : Continuous fun x => F x y)

theorem res_heisO_continuous_bounded : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 →
    ∀ f, IsThetaFunO ψ V W f →
    Continuous (fun p : WO V' W × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f) p.1) ∧
    ∃ M : ℝ, ∀ x u, ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x‖ ≤ M := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h𝓨 f hf
  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  have hfin : μ 𝓨 < ⊤ := by rw [h𝓨.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨-, -, j3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (Mx D W.rank r) := BorelSpace.opensMeasurable
  haveI : SecondCountableTopology (WO V' W × Mx D W.rank r) := @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _ j3 i3
  haveI : FirstCountableTopology (WO V' W × Mx D W.rank r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hiso : ∀ (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E),
      Continuous (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C₀) := fun C₀ =>
    Continuous.matrix_mul continuous_id continuous_const
  have hmid : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B) :=
    Continuous.matrix_mul continuous_id continuous_const
  have hFb : ∀ (p : WO V' W × Mx D W.rank r) (y : Mx D W.rank r),
      ‖heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f
        (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B p.1)‖ ≤ K := fun p y => by
    simp only [heisO, norm_mul, hn, one_mul]
    exact hK _
  have ha : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C q.2 + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B q.1.1 :=
    ((hiso C).comp continuous_snd).add (hmid.comp (continuous_fst.comp continuous_fst))
  have hb : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' q.1.2 := (hiso C').comp (continuous_snd.comp continuous_fst)
  have hFc : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' q.1.2) f
        (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C q.2 + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B q.1.1) :=
    (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH ha hb)).mul (hf.cont.comp (ha.add hb))
  have h := continuous_bounded_setIntegral μ 𝓨 hfin _ hFc K hFb
  exact ⟨h.1, _, fun x u => h.2 (x, u)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ResCont

end
