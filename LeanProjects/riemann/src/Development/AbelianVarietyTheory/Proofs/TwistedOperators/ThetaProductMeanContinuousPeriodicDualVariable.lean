import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistThetaMean

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a b : Mx D W.rank r) :
    isoPart V W C (a + b) = isoPart V W C a + isoPart V W C b :=
  Matrix.add_mul _ _ _

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {γ : Mx D W.rank r}
    (hγ : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨g * (adj D C * V.gram), ?_⟩
  show (g * (adj D C * V.gram)).map (incA D) = g.map (incA D) * (adj D C * V.gram).map (incA D)
  exact Matrix.map_mul

theorem isoPart_continuous (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) :=
  continuous_id.matrix_mul continuous_const

theorem midPart_continuous (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    Continuous (midPart V V' W B) :=
  continuous_id.matrix_mul continuous_const

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

theorem integral_continuous_of_bounded {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : X × Y → ℂ) (hk : Continuous k) (b : ℝ) (hb : ∀ q, ‖k q‖ ≤ b) :
    Continuous (fun p => ∫ y, k (p, y) ∂ν) ∧ ∀ p, ‖∫ y, k (p, y) ∂ν‖ ≤ b * ν.real Set.univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => b) (fun p => ?_) (fun p => ?_) (integrable_const _) ?_,
    fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hb _)⟩
  · exact (hk.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hb _
  · exact Filter.Eventually.of_forall fun y => hk.comp (Continuous.prodMk_left y)

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

open TopologicalSpace in

theorem mean_continuous_periodic : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B _hs C' _h1 _h2 _h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' h𝓕' P G hP hG
  haveI hAE : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI hM : SecondCountableTopology (Mx D W.rank r) :=
    inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin r → AE D))
  haveI hM2 : SecondCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    @instSecondCountableTopologyProd _ _ _ _ hM hM
  haveI : FirstCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    SecondCountableTopology.to_firstCountableTopology _
  haveI : FirstCountableTopology (Mx D W.rank r) := SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V'
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO V' W) (ratL W V') hK hKc μ' h𝓕'⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by
    rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b1, hb1⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hP
  obtain ⟨b2, hb2⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hh : Continuous fun w => P w * star (G w) := hP.cont.mul hG.cont.star
  have hhb : ∀ w, ‖P w * star (G w)‖ ≤ b1 * b2 := fun w => by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb1 w) (hb2 w) (norm_nonneg _) ((norm_nonneg _).trans (hb1 w))
  have hu : Continuous fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2 :=
    (((isoPart_continuous V W C').comp (continuous_fst.comp continuous_fst)).add
      ((isoPart_continuous V W C).comp (continuous_snd.comp continuous_fst))).add
      ((midPart_continuous V V' W B).comp continuous_snd)
  obtain ⟨hin, hinb⟩ := integral_continuous_of_bounded (μ'.restrict 𝓕')
    (fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      P (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2) *
        star (G (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2))) (hh.comp hu) (b1 * b2)
    (fun q => hhb _)
  refine ⟨?_, ?_⟩
  · exact (integral_continuous_of_bounded (μ.restrict 𝓨)
      (fun q : Mx D W.rank r × Mx D W.rank r => ∫ x in 𝓕',
        P (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x) *
          star (G (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x)) ∂μ') hin _ hinb).1
  · intro γ hγ t
    have key : ∀ y x, P (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x)) =
        P (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' t + isoPart V W C y + midPart V V' W B x)) := fun y x => by
      rw [isoPart_add, add_assoc (isoPart V W C' γ) (isoPart V W C' t),
        add_assoc (isoPart V W C' γ) (isoPart V W C' t + isoPart V W C y)]
      exact GlobalTheory.ThetaSchur.prod_periodic hψ hP hG (isoPart_rat V W C' hγ) _
    simp_rw [key]

end GlobalTheory.TwistThetaMean
