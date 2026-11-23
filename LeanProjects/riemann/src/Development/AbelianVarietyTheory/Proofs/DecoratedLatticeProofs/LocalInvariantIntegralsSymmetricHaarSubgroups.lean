import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarIsMulLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapHaarFiniteOnCompactsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapPreimageIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulLeftInvariantMapLevyProductMapToFourierJacoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompactsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevyProductMapToFourierJacobiPreimageIntegralGLStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.HaarR
open scoped ENNReal NNReal

theorem eq_of_mass_one {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (κ μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts κ] [κ.IsMulLeftInvariant] (S : Set G) (hS : μ S = 1) (hκ : κ S = 1) : κ = μ := by
  have h := Measure.isMulLeftInvariant_eq_smul κ μ
  set a := Measure.haarScalarFactor κ μ
  have h1 : (a : ℝ≥0∞) = 1 := by
    rw [h, Measure.smul_apply, hS, ENNReal.smul_def, smul_eq_mul, mul_one] at hκ
    exact hκ
  have : a = 1 := by exact_mod_cast h1
  rw [h, this, one_smul]

theorem quot_int_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (m : Measure (GL n k)) (G : Measure (GL (n ⊕ Fin c) k)), m.IsHaarMeasure → G.IsHaarMeasure → m (KO k n) = 1 → (c + 1 = 2 * ρ → ∀ μR : Measure (R k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotInt ν m G ρ f z → IsQuotIntL1 μR G f z) ∧ (1 ≤ ρ → c = 2 * ρ → ∀ μR : Measure (RFJ k n c ρ), μR.IsHaarMeasure → μR {x | x.1 ∈ KO k (n ⊕ Fin c)} = 1 → μR.IsInvInvariant ∧ ∀ f z, IsQuotIntFJ ν m G ρ f z → IsQuotIntL1 μR G f z) := by
  intro k _ _ _ _ _ _ ν hν n _ _ c ρ m G hm hG hmK
  haveI := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  have hKO : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), MeasurableSet {x : S | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} :=
    fun S => (GlobalTheory.SplitFlip.isOpen_KO.preimage continuous_subtype_val).measurableSet
  have hFint : ∀ F ∈ SB (GL (n ⊕ Fin c) k), Integrable F G := fun F hF => hF.1.continuous.integrable_of_hasCompactSupport hF.2
  have hFS : ∀ (S : Subgroup (GL (n ⊕ Fin c) k)), IsClosed (S : Set (GL (n ⊕ Fin c) k)) → ∀ (μS : Measure S),
      μS.IsHaarMeasure → ∀ F ∈ SB (GL (n ⊕ Fin c) k), ∀ h, Integrable (fun r : S => F (r * h)) μS := by
    intro S hS μS _ F hF h
    exact (hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)).integrable_of_hasCompactSupport
      ((hF.2.comp_homeomorph (Homeomorph.mulRight h)).comp_isClosedEmbedding hS.isClosedEmbedding_subtypeVal)
  refine ⟨fun hc μR hR hRK => ?_, fun h1 hc μR hR hRK => ?_⟩
  · have h1 : 1 ≤ ρ := by omega
    have h2 : ρ ≤ c := by omega
    obtain ⟨hNc, hcl, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c ρ h1 h2 ν
    haveI : LocallyCompactSpace (N k n c ρ) := hNc.locallyCompactSpace
    haveI := hNH
    haveI : LocallyCompactSpace (R k n c ρ) := hcl.locallyCompactSpace
    haveI := hR
    haveI := hm
    haveI := GlobalTheory.T.levyProductMap_haar_isMulLeftInvariant k n c ρ h1 h2 ν hν.1 m hm
    haveI := GlobalTheory.T.levyProductMap_haar_finiteOnCompacts k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodR (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)) _).measurable
    have hκ : (m.prod (volN ν n c ρ)).map (prodR ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (R k n c ρ))).trans ?_)
      rw [GlobalTheory.T.levyProductMap_preimage_integralGL, Measure.prod_prod, hmK, GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c ρ h1 h2 ν hν, one_mul]
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c ρ (fun i => i.val + 1)
      (fun i => by simp [Fin.rev]; omega) (R k n c ρ)
      (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).1 μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : R k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodR (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h)) (m.prod (volN ν n c ρ)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp]
    rfl
  · have h2 : ρ < c := by omega
    obtain ⟨hNc, -, hNH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν
    haveI : LocallyCompactSpace (N k n c (ρ + 1)) := hNc.locallyCompactSpace
    haveI := hNH
    haveI := hm
    haveI := hR
    have hmem := (GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n c ρ).2 h1 h2
    have hcl : IsClosed (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) := by
      have e : (RFJ k n c ρ : Set (GL (n ⊕ Fin c) k)) = ⋂ r : n ⊕ Fin c, ⋂ s : n ⊕ Fin c,
          {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
        ext g; simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
      rw [e]
      refine isClosed_iInter fun r => isClosed_iInter fun s => ?_
      by_cases hrs : (r.isRight ∨ s.isRight) ∧ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
          Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} =
            {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
          ext g; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hrs.1 hrs.2, fun h _ _ => h⟩
        rw [this]
        exact isClosed_eq (GlobalTheory.RootEx.VolN.continuous_entry r s) continuous_const
      · have : {g : GL (n ⊕ Fin c) k | (r.isRight ∨ s.isRight) →
            Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤
              Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r →
            g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} = Set.univ := by
          ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact fun a b => absurd ⟨a, b⟩ hrs
        rw [this]; exact isClosed_univ
    haveI : LocallyCompactSpace (RFJ k n c ρ) := hcl.locallyCompactSpace
    haveI := GlobalTheory.T.isMulLeftInvariant_map_levyProductMapToFourierJacobi k n c ρ h1 h2 ν hν.1 m hm
    haveI := GlobalTheory.T.fourierJacobiProductMap_haar_finiteOnCompacts k n c ρ h1 h2 ν hν.1 m hm
    have hmeas : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) :=
      (Continuous.subtype_mk (((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_fst.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
        ((GlobalTheory.RootEx.QuotStep.continuous_colE (ρ + 1)).comp continuous_snd)) _).measurable
    have hκ : ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ) = μR := by
      refine eq_of_mass_one _ μR _ hRK ((Measure.map_apply hmeas (hKO (RFJ k n c ρ))).trans ?_)
      have hpi : {β : n → k | ∀ i, β i ∈ 𝒪[k]} = Set.univ.pi fun _ : n => (𝒪[k] : Set k) := by
        ext β; simp
      rw [GlobalTheory.T.levyProductMapToFourierJacobi_preimage_integralGL k n c ρ h2, Measure.prod_prod, Measure.prod_prod, hmK, GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c (ρ + 1) (by omega) (by omega) ν hν, hpi,
        Measure.pi_pi, hν.2]
      simp
    haveI : μR.IsMulRightInvariant := GlobalTheory.LevelUnimod.unimodular k n c (2 * ρ + 1) (fun i => 2 * (i.val + 1))
      (fun i => by simp [Fin.rev]; omega) (RFJ k n c ρ) hmem μR hR
    refine ⟨GlobalTheory.SemiHaar.invInv_of_rightInv μR, ?_⟩
    rintro f z ⟨F, hF, hf, hz⟩
    have hi := hFS _ hcl μR hR F hF
    refine ⟨F, hFint F hF, hi, fun h => ?_, hz⟩
    have hc' : Continuous fun r : RFJ k n c ρ => F (r * h) :=
      hF.1.continuous.comp (continuous_subtype_val.mul continuous_const)
    have hp : Integrable (fun q => F ((prodRFJ (k := k) (n := n) (c := c) ρ q : GL (n ⊕ Fin c) k) * h))
        ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
      have := hi h
      rw [← hκ] at this
      exact (integrable_map_measure hc'.aestronglyMeasurable hmeas.aemeasurable).1 this
    rw [hf h, ← hκ, integral_map hmeas.aemeasurable hc'.aestronglyMeasurable, integral_prod _ hp,
      integral_prod _ hp.integral_prod_left]
    rfl

end GlobalTheory.HaarR
