import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMeasurePushforwardEqProductRealMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslates
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFrameMemUH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetDisint

theorem integral_eq_of_lintegral_eq {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (m : Measure Y)
    (f : X → ℂ) (g : Y → ℂ) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ c : ℂ → ENNReal, Measurable c → ∫⁻ x, c (f x) ∂μ = ∫⁻ y, c (g y) ∂m) (hi : Integrable f μ) :
    Integrable g m ∧ ∫ x, f x ∂μ = ∫ y, g y ∂m := by
  have e : μ.map f = m.map g := by
    ext S hS
    rw [Measure.map_apply hf hS, Measure.map_apply hg hS]
    have h1 := h (S.indicator 1) (measurable_one.indicator hS)
    have e1 : ∀ x, S.indicator (1 : ℂ → ENNReal) (f x) = (f ⁻¹' S).indicator 1 x := fun x => by
      by_cases hx : f x ∈ S <;> simp [Set.indicator, hx]
    have e2 : ∀ y, S.indicator (1 : ℂ → ENNReal) (g y) = (g ⁻¹' S).indicator 1 y := fun y => by
      by_cases hy : g y ∈ S <;> simp [Set.indicator, hy]
    simp only [e1, e2] at h1
    rwa [lintegral_indicator_one (hf hS), lintegral_indicator_one (hg hS)] at h1
  refine ⟨?_, ?_⟩
  · have h1 : Integrable (fun z : ℂ => z) (μ.map f) :=
      (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).2 hi
    rw [e] at h1
    exact (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).1 h1
  · have a1 := integral_map (μ := μ) hf.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    have a2 := integral_map (μ := m) hg.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    rw [← a1, ← a2, e]

variable {D : D7}

theorem continuous_realPt {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} (hW : W.SigOK) {Fr : Frames W}
    (hFr : IsFrames W Fr) : Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  obtain ⟨h1, -, -, -, -⟩ := Formalism.IndefR.Eqv.ga_facts D W
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hm : Continuous fun b : (∀ ρ, Upq W ρ) => UpqT.mat (b ρ) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply ρ)
  refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous
    (continuous_const.matrix_mul ((continuous_const.matrix_mul hm).matrix_mul continuous_const)) fun b => ?_
  refine conjFrame_mem_UH _ _ _ (sig_sum W hW (tauE D ρ)) _ _ (hFr ρ) ?_ (b ρ)
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND W).2).isUnit

theorem finE_toFin (W : HSp D) (h : GA D W) : finE W h = finE W (GlobalTheory.AutMult.toFin W h : GA D W) := by
  conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin h]
  rw [map_mul]
  have : finE W (GlobalTheory.AutMult.toInf W h : GA D W) = 1 := by
    show Formalism.UG.bc (swapAE D) (finHom W _) = 1
    rw [MonoidHom.mem_ker.1 (GlobalTheory.AutMult.toInf W h).2, map_one]
  rw [this, one_mul]

end GlobalTheory.CosetDisint

end

namespace GlobalTheory.CosetDisint

theorem integral_eq_cosetSum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν hO Fr hFr mR hmR Z hZc hZi hZinv
  obtain ⟨i0, -, -, i3, i4⟩ := Formalism.IndefR.Eqv.ga_facts D W
  haveI := i0; haveI := i3; haveI := i4
  haveI : ν.IsHaarMeasure := hν.1
  haveI := Formalism.IndefR.Eqv.gfC_secondCountable D W
  set O : Set (GA D W) := {h | finE W h ∈ K} with hOdef
  have hOm : MeasurableSet O := hO.measurableSet
  set φ : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hφdef
  have hφ : Continuous φ := continuous_realPt hθ hW hFr
  have hZm : Measurable Z := hZc.measurable
  set L' := (levA W K).subgroupOf (GfC W) with hL'
  have hmemL : ∀ y : GfC W, y ∈ L' ↔ finE W (y : GA D W) ∈ K := fun y => by
    rw [hL', Subgroup.mem_subgroupOf, mem_levA]
    exact and_iff_right y.2
  have hL'o : IsOpen (L' : Set (GfC W)) := by
    have : (L' : Set (GfC W)) = Subtype.val ⁻¹' O := Set.ext fun y => hmemL y
    rw [this]; exact hO.preimage continuous_subtype_val

  haveI : Countable (GfC W ⧸ L') := by
    have hpd : (Set.univ : Set (GfC W ⧸ L')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (L' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hL'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [L'.one_mem]⟩))

  let s : GfC W ⧸ L' → Set (GA D W) := fun q => (fun g => (FinCos.rep q)⁻¹ * g) ⁻¹' O
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (GlobalTheory.AutMult.toFin W g) := by
    intro q g
    show finE W ((FinCos.rep q)⁻¹ * g) ∈ K ↔ _
    rw [finE_toFin, map_mul, map_inv, FinCos.rep, GlobalTheory.AutMult.toFin_coe, ← hmemL]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hOm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  have key : ∀ q : GfC W ⧸ L', ∀ G : GA D W → ENNReal, Measurable G → (∀ g, ∀ k ∈ levA W K, G (g * k) = G g) →
      ∫⁻ g in s q, G g ∂ν = ∫⁻ b, G (FinCos.rep q * φ b) ∂(Measure.pi mR) := by
    intro q G hG hGi
    have hpre : (fun h => FinCos.rep q * h) ⁻¹' s q = O := by
      ext h; simp [s]
    rw [← (measurePreserving_mul_left ν (FinCos.rep q)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft _) G (s q), hpre]
    exact GlobalTheory.T.level_measure_pushforward_eq_product_real_measures D θ hθ W hW K ν hν Fr hFr mR hmR (fun h => G (FinCos.rep q * h)) (hG.comp (measurable_const_mul _))
      (fun g k hk => by simp only [← mul_assoc]; exact hGi _ k hk) hOm
  have hcm : ∀ q : GfC W ⧸ L', Continuous fun b => Z (FinCos.rep q * φ b) := fun q =>
    hZc.comp (continuous_const.mul hφ)

  have hlin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) = ∫⁻ g, ‖Z g‖ₑ ∂ν := by
    rw [lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]
    rw [← Measure.restrict_univ (μ := ν), ← hU, lintegral_iUnion hsm hd]
    refine tsum_congr fun q => (key q (fun g => ‖Z g‖ₑ) hZm.enorm fun g k hk => by rw [hZinv g k hk]).symm
  have hfin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) < ⊤ := by
    rw [hlin]; exact hZi.2
  refine ⟨hfin, ?_⟩

  have hint : ∀ q : GfC W ⧸ L', ∫ g in s q, Z g ∂ν = ∫ b, Z (FinCos.rep q * φ b) ∂(Measure.pi mR) := fun q =>
    (integral_eq_of_lintegral_eq (ν.restrict (s q)) (Measure.pi mR) Z _ hZm (hcm q).measurable
      (fun c hc => key q (fun g => c (Z g)) (hc.comp hZm) fun g k hk => by simp only [hZinv g k hk])
      hZi.integrableOn).2
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hZi.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  rw [← hsum.tsum_eq, integral_tsum (fun q => (hcm q).aestronglyMeasurable)
    (by rw [← lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]; exact hfin.ne)]
  exact tsum_congr hint

end GlobalTheory.CosetDisint
