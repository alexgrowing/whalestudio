import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeigStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_heis_apply (hom : IsWeilDatumO ψ S T χS χT om) (p : GA D S × GA D T) (u : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    om p (heisO ψ S T u f) x = ψ (symplOH S T x (actO S T p.1 p.2 u)) * om p f (x + actO S T p.1 p.2 u) := by
  obtain ⟨g, h⟩ := p
  rw [hom.om_heis g h u f hf]; rfl

theorem om_heis_bound (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ (C : ℝ) (A : ℕ), ∀ g h u x, ‖om (g, h) (heisO ψ S T u f) x‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight D ψ S T χS χT om hom f hf
  refine ⟨C, A, fun g h u x => ?_⟩
  rw [om_heis_apply hom (g, h) u hf x, norm_mul, hom.std.1.2.1, one_mul]
  exact hC g h _

theorem continuous_actO_gen {X : Type} [TopologicalSpace X] {g : X → GA D S} {h : X → GA D T} {u : X → WO S T}
    (hg : Continuous g) (hh : Continuous h) (hu : Continuous u) : Continuous fun t => actO S T (g t) (h t) (u t) := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  unfold actO
  exact (((hmt T).comp hh).matrix_mul hu).matrix_mul ((hmti S).comp hg)

theorem continuous_om_heis (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => om q.1.1 (heisO ψ S T q.2 f) q.1.2 := by
  have hJ : Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 f p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ S T χS χT om hom f hf
  have hA : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => actO S T q.1.1.1 q.1.1.2 q.2 := by
    exact continuous_actO_gen (continuous_fst.comp (continuous_fst.comp continuous_fst))
      (continuous_snd.comp (continuous_fst.comp continuous_fst)) continuous_snd
  have hB : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ((q.1.1, q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) : (GA D S × GA D T) × WO S T) :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).add hA)
  have hc : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ψ (symplOH S T q.1.2 (actO S T q.1.1.1 q.1.1.2 q.2)) * om q.1.1 f (q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) :=
    (hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.comp continuous_fst) hA)).mul (hJ.comp hB)
  exact hc.congr fun q => (om_heis_apply hom q.1.1 q.2 hf q.1.2).symm

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_superpos (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p : GA D S × GA D T) (m' : Measure (WO S T)) [SFinite m'] (α : WO S T → ℂ) (hα : Integrable α m')
    (hI : IsThetaFunO ψ S T (fun x => ∫ u, α u * heisO ψ S T u f x ∂m')) (x : WO S T) :
    om p (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') x = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hφ : AEMeasurable (fun u : WO S T => (u, α u)) m' := measurable_id.aemeasurable.prodMk hα.aemeasurable
  set ν : Measure (WO S T × ℂ) := m'.map (fun u => (u, α u)) with hν
  obtain ⟨C1, hC1⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std f hf
  obtain ⟨C2, hC2⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std _ (hom.om_pres p f hf)
  set F : WO S T × ℂ → WO S T → ℂ := fun z => z.2 • heisO ψ S T z.1 f with hF
  have hFth : ∀ z, IsThetaFunO ψ S T (F z) := fun z =>
    GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf z.1)
  have hc1 : Continuous (Function.uncurry F) := by
    have e : Function.uncurry F = fun q : (WO S T × ℂ) × WO S T => q.1.2 * (ψ (symplOH S T q.2 q.1.1) * f (q.2 + q.1.1)) := by
      funext q; rfl
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd
      (continuous_fst.comp continuous_fst))).mul (hf.cont.comp (continuous_snd.add (continuous_fst.comp continuous_fst))))
  have hc2 : Continuous fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2 := by
    have e : (fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2) =
        fun q => q.1.2 * om p (heisO ψ S T q.1.1 f) q.2 := by
      funext q; simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((continuous_om_heis hom hf).comp
      ((continuous_const.prodMk continuous_snd).prodMk (continuous_fst.comp continuous_fst)))
  have hβ : Integrable (fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2) ν := by
    have hm : Continuous fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2 := (continuous_norm.comp continuous_snd).mul continuous_const
    rw [hν, integrable_map_measure hm.measurable.aestronglyMeasurable hφ]
    exact hα.norm.mul_const _
  have hdom : ∀ z y, ‖F z y‖ ≤ ‖z.2‖ * max C1 C2 ∧ ‖om p (F z) y‖ ≤ ‖z.2‖ * max C1 C2 := by
    intro z y
    constructor
    · show ‖z.2 * (ψ (symplOH S T y z.1) * f (y + z.1))‖ ≤ _
      rw [norm_mul, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC1 _).trans (le_max_left _ _)) (norm_nonneg _)
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
      obtain ⟨g, h⟩ := p
      rw [norm_mul, om_heis_apply hom (g, h) z.1 hf y, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC2 _).trans (le_max_right _ _)) (norm_nonneg _)
  have hint : ∀ y, ∫ z, F z y ∂ν = ∫ u, α u * heisO ψ S T u f y ∂m' := by
    intro y
    rw [hν, integral_map hφ]
    · rfl
    · exact (hc1.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hint2 : ∫ z, om p (F z) x ∂ν = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
    rw [hν, integral_map hφ]
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    · exact (hc2.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hI' : IsThetaFunO ψ S T (fun y => ∫ z, F z y ∂ν) := by
    simp only [hint]; exact hI
  have key := GlobalTheory.CommIntBdd.om_integral_comm_dom D ψ S T χS χT om hom (WO S T × ℂ) ν F p
    (fun z => ‖z.2‖ * max C1 C2) hFth hc1 hc2 hβ hdom hI' x
  have e : (fun w' => ∫ z, F z w' ∂ν) = fun y => ∫ u, α u * heisO ψ S T u f y ∂m' := funext hint
  rw [← hint2, ← key, e]

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

theorem kernel_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T),
    Measurable c → Continuous g → Continuous h → Continuous w →
    (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) →
    (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧
      Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  intro D ψ S T χS χT om hom Y _ _ _ _ m _ c g h w hc hg hh hw hint
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hgh : Continuous fun y => ((g y, h y) : GA D S × GA D T) := hg.prodMk hh

  have hK : ∀ f, IsThetaFunO ψ S T f →
      Continuous fun q : Y × WO S T => om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1) := fun f hf =>
    (continuous_om_heis hom hf).comp (((hgh.comp continuous_fst).prodMk (hw.comp continuous_fst)).prodMk continuous_snd)
  have hbd : ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ y u,
      ‖c y * om (g y, h y) (heisO ψ S T u f) (w y)‖ ≤ C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by
    intro f hf
    obtain ⟨C, A, hC⟩ := om_heis_bound hom hf
    refine ⟨C, A, fun y u => ?_⟩
    rw [norm_mul]
    calc ‖c y‖ * ‖om (g y, h y) (heisO ψ S T u f) (w y)‖
        ≤ ‖c y‖ * (C * (quotHeight S (g y) * quotHeight T (h y)) ^ A) :=
          mul_le_mul_of_nonneg_left (hC _ _ _ _) (norm_nonneg _)
      _ = C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by ring
  have hintH : ∀ f, IsThetaFunO ψ S T f → ∀ u,
      Integrable (fun y => c y * om (g y, h y) (heisO ψ S T u f) (w y)) m := by
    intro f hf u
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact Integrable.mono' ((hint A).const_mul C)
      (hc.aestronglyMeasurable.mul ((hK f hf).comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable)
      (ae_of_all _ fun y => hC y u)
  have hzero : ∀ f : WO S T → ℂ, heisO ψ S T 0 f = f := by
    intro f; funext x; simp [heisO, symplOH, symplO, hO]
  have hintK : ∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m := by
    intro f hf
    simpa only [hzero] using hintH f hf 0
  refine ⟨hintK, ?_, ?_, ?_, ?_, ?_⟩
  · intro f f' hf hf'
    simp only [map_add, Pi.add_apply, mul_add]
    exact integral_add (hintK f hf) (hintK f' hf')
  · intro a f hf
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    refine continuous_of_dominated (bound := fun y => C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A))
      (fun u => (hintH f hf u).aestronglyMeasurable) (fun u => ae_of_all _ fun y => hC y u) ((hint A).const_mul C)
      (ae_of_all _ fun y => ?_)
    exact continuous_const.mul ((hK f hf).comp (continuous_const.prodMk continuous_id))
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact ⟨∫ y, C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) ∂m, fun u =>
      norm_integral_le_of_norm_le ((hint A).const_mul C) (ae_of_all _ fun y => hC y u)⟩
  · intro f hf m' _ α hα hI
    have e1 : ∀ y, om (g y, h y) (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') (w y) =
        ∫ u, α u * om (g y, h y) (heisO ψ S T u f) (w y) ∂m' := fun y =>
      om_superpos hom hf (g y, h y) m' α hα hI (w y)
    simp only [e1]
    simp only [← integral_const_mul]
    rw [integral_integral_swap]
    · refine integral_congr_ae (ae_of_all _ fun u => ?_)
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only
      ring
    · obtain ⟨C, A, hC⟩ := hbd f hf
      refine Integrable.mono' (((hint A).const_mul C).mul_prod hα.norm) ?_ (ae_of_all _ fun q => ?_)
      · exact (hc.aestronglyMeasurable.comp_fst).mul (hα.aestronglyMeasurable.comp_snd.mul
          (hK f hf).measurable.aestronglyMeasurable)
      · calc ‖c q.1 * (α q.2 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1))‖
            = ‖c q.1 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1)‖ * ‖α q.2‖ := by
              simp only [norm_mul]; ring
          _ ≤ C * (‖c q.1‖ * (quotHeight S (g q.1) * quotHeight T (h q.1)) ^ A) * ‖α q.2‖ :=
              mul_le_mul_of_nonneg_right (hC _ _) (norm_nonneg _)

end GlobalTheory.KerTame
