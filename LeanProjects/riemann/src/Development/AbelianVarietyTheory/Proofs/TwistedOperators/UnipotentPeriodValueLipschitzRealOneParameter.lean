import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableScalarActionMultiplicityMapValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.LipValue

theorem lip_value : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Is θ d Q → ∀ (J : Set (GA D Y)) (χ : GA D Y → ℂ), ∀ t ∈ MultT θ M₀ J χ, ∀ b : ℝ, (∀ x, ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b) → Lip θ p.A (t (PiTensorProduct.tprod ℂ p.w)) (Real.exp Q * b) := by
  intro hCusp D θ hθ Y V d S S' M₀ M p Q hp J χ t ht b hb
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D Y
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  obtain ⟨c, hc⟩ := hp.2 (Measure.haar : Measure (GinfC Y)) inferInstance
  set m : Measure (GinfC Y) := Measure.haar with hm
  set φ : GA D Y → ℂ := t (PiTensorProduct.tprod ℂ p.w) with hφ
  set α : GinfC Y → ℂ := fun h => coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y)) with hα
  have hαi : Integrable α m := by simpa only [one_mul] using (hc.far 1).1
  have hrep := GlobalTheory.T.integrable_scalar_action_multiplicityMap_values hCusp D θ hθ Y S' M₀ J χ t ht p.w m inferInstance α c hαi hc.act

  have hT := (mem_multT θ M₀ J χ t).1 ht
  have hcont : Continuous φ := by
    have key : ∀ T ∈ Mult θ M₀ J χ, Continuous (T p.w) := by
      intro T hT'
      induction hT' using Submodule.span_induction with
      | mem T h => exact (h.aut p.w).cont
      | zero => exact continuous_const
      | add T T' _ _ h h' => exact h.add h'
      | smul a T _ h => exact h.const_smul a
    have := key _ hT
    simpa [PiTensorProduct.lift_symm] using this
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 1)
  intro x τ X hX s
  let k : GinfC Y := ⟨oneP θ Y τ X s, GlobalTheory.PointAtPlaceHom.atTau_mem Y τ _⟩
  have hkinv : ((k⁻¹ : GinfC Y) : GA D Y) = oneP θ Y τ X (-s) := by
    show (oneP θ Y τ X s)⁻¹ = _
    exact inv_eq_of_mul_eq_one_right (by
      rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ])
  have hmeas : ∀ y : GA D Y, AEStronglyMeasurable (fun h : GinfC Y => φ (y * h)) m := fun y =>
    (hcont.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  have hbd : ∀ y : GA D Y, ∀ᵐ (h : GinfC Y) ∂m, ‖φ (y * h)‖ ≤ b := fun y => Filter.Eventually.of_forall fun h => hb _
  have hαk : Integrable (fun h => α (k⁻¹ * h)) m := hαi.comp_mul_left k⁻¹
  have hI1 : Integrable (fun h => α (k⁻¹ * h) * φ (x * h)) m := hαk.mul_bdd (hmeas x) (hbd x)
  have hI0 : Integrable (fun h => α h * φ (x * h)) m := hαi.mul_bdd (hmeas x) (hbd x)
  have h1 : c * φ (x * k) = ∫ h, α (k⁻¹ * h) * φ (x * h) ∂m := by
    rw [← hrep (x * k)]
    have := integral_mul_left_eq_self (μ := m) (fun h => α (k⁻¹ * h) * φ (x * h)) k
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show α h * φ (x * ↑k * ↑h) = α (k⁻¹ * (k * h)) * φ (x * ↑(k * h))
    rw [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]
  have hdiff : c * (φ (x * k) - φ x) = ∫ h, (α (k⁻¹ * h) - α h) * φ (x * h) ∂m := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hI1 hI0]
    congr 1
    funext h
    ring
  have hlip := hc.lip τ X hX (-s)
  have hlip' : ∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m ≤ Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹) := by
    have e : (fun h : GinfC Y => ‖α (k⁻¹ * h) - α h‖) = fun h : GinfC Y =>
        ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X (-s) * h)) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)‖ := by
      funext h
      simp only [hα, Subgroup.coe_mul, hkinv]
    rw [e]
    simpa only [abs_neg] using hlip
  have hint : Integrable (fun h => ‖α (k⁻¹ * h) - α h‖) m := (hαk.sub hαi).norm
  have hnorm : ‖c‖ * ‖φ (x * k) - φ x‖ ≤ (∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m) * b := by
    rw [← norm_mul, hdiff, ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun h => norm_nonneg _) (hint.mul_const b) (Filter.Eventually.of_forall fun h => ?_))
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc.ne
  have hH : 0 ≤ hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹) := Real.sqrt_nonneg _
  have key : ‖c‖ * ‖φ (x * k) - φ x‖ ≤ ‖c‖ * (Real.exp Q * b * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) := by
    refine hnorm.trans ?_
    calc (∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m) * b
        ≤ (Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) * b := mul_le_mul_of_nonneg_right hlip' hb0
      _ = ‖c‖ * (Real.exp Q * b * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) := by ring
  exact le_of_mul_le_mul_left key hc0

end GlobalTheory.SepPer.LipValue

end
