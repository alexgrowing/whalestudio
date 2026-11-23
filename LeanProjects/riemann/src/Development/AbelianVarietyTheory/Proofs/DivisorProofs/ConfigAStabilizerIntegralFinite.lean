import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseASecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseAThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationTriplePeriodCaseAFourthStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKOpCont

theorem continuous_iter_integral {Y Kt L : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    [TopologicalSpace Kt] [FirstCountableTopology Kt] [MeasurableSpace Kt] [OpensMeasurableSpace Kt]
    [MeasurableSpace L] {μK : Measure Kt} [IsFiniteMeasure μK] {μ : Measure L}
    (f : Kt → L → Y → ℂ)
    (hy : ∀ k l, Continuous (f k l))
    (hk : ∀ l y, Continuous fun k => f k l y)
    (hl : ∀ k y, AEStronglyMeasurable (fun l => f k l y) μ)
    (hdom : ∀ y₀, ∃ U ∈ 𝓝 y₀, ∃ G : L → ℝ, Integrable G μ ∧ ∀ k l, ∀ y ∈ U, ‖f k l y‖ ≤ G l) :
    Continuous fun y => ∫ k, ∫ l, f k l y ∂μ ∂μK := by
  have hin : ∀ k, Continuous fun y => ∫ l, f k l y ∂μ := by
    intro k
    refine continuous_iff_continuousAt.2 fun y₀ => ?_
    obtain ⟨U, hU, G, hG, hb⟩ := hdom y₀
    exact continuousAt_of_dominated (Eventually.of_forall fun y => hl k y)
      (eventually_of_mem hU fun y hy => Eventually.of_forall fun l => hb k l y hy) hG
      (Eventually.of_forall fun l => (hy k l).continuousAt)
  have hink : ∀ y, Continuous fun k => ∫ l, f k l y ∂μ := by
    intro y
    refine continuous_iff_continuousAt.2 fun k₀ => ?_
    obtain ⟨U, hU, G, hG, hb⟩ := hdom y
    exact continuousAt_of_dominated (Eventually.of_forall fun k => hl k y)
      (Eventually.of_forall fun k => Eventually.of_forall fun l => hb k l y (mem_of_mem_nhds hU)) hG
      (Eventually.of_forall fun l => (hk l y).continuousAt)
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  obtain ⟨U, hU, G, hG, hb⟩ := hdom y₀
  refine continuousAt_of_dominated (bound := fun _ => ∫ l, G l ∂μ)
    (Eventually.of_forall fun y => (hink y).aestronglyMeasurable) ?_ (integrable_const _)
    (Eventually.of_forall fun k => (hin k).continuousAt)
  refine eventually_of_mem hU fun y hy => Eventually.of_forall fun k => ?_
  exact norm_integral_le_of_norm_le hG (Eventually.of_forall fun l => hb k l y hy)

theorem continuous_weilOp_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      Continuous (fun y => ∫ k, ∫ l, om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  obtain ⟨c, g, hg1, hg2, hint⟩ := GlobalTheory.T.evaluation_triple_period_case_a hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ x
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  have hsp := hw.isUSplitting
  have hstd : IsStd B.ψ := hT.base.std

  have hom : ∀ k : UA σ G.V.J, om (g.1 * k, g.2) Ψ = om (g.1 * k, 1) (om (1, g.2) Ψ) := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

  have hact : ∀ l : (AE F E)ˣ, actAB (cA σ) g (shiftA H H' l) = shiftA H H' l := by
    intro l
    simp only [actAB, shiftA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose]
    change l.1 • Matrix.vecMulVec (mat g.1 *ᵥ incV F H.x) (mat g.2 *ᵥ incV F H'.y) = _
    rw [hg1, hg2]
  have hF : ∀ (k : UA σ G.V.J) (l : (AE F E)ˣ), om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ))) =
      c • e (G.M.co.rho B.ψ (shiftA H H' l) (om (g.1 * k, g.2) Ψ)) := by
    intro k l
    have hm : om (k, 1) Ψ ∈ schA F _ := hsp.pres _ _ hΨ
    rw [hint _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hm), hsp.impl g _ _ hm, hact l,
      ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [hF, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  refine continuous_const.mul ?_

  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨i1, -, i3, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (b + 2) G.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : FirstCountableTopology K := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun k => (hK k).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V k).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI := hμK
  haveI : IsFiniteMeasure μK := inferInstance
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  set Ψ₁ := om (1, g.2) Ψ with hΨ₁
  have hΨ₁m : Ψ₁ ∈ schA F _ := hsp.pres _ _ hΨ
  have hD : ∀ (k : UA σ G.V.J) (l : (AE F E)ˣ),
      e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, 1) Ψ₁)) ∈ schA F (Fin b × Fin (b + a')) := fun k l =>
    he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ (hsp.pres _ _ hΨ₁m))
  simp only [hom]
  have hν : Continuous fun l : (AE F E)ˣ => ((X.ν l : Circle) : ℂ) := by
    have h1 := hT.chars.heckeα.1
    have h2 := hT.chars.heckeβ.1
    have h3 : (fun l : (AE F E)ˣ => ((X.ν l : Circle) : ℂ)) = fun l => ((X.α l / X.β l : Circle) : ℂ) := by
      funext l; rfl
    rw [h3]
    exact continuous_subtype_val.comp (h1.div' h2)
  have hab : Continuous fun l : (AE F E)ˣ => (((absE F E l : ℝ) : ℂ)) ^ ((b + 2 - a') / 2) :=
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE))).pow _
  refine continuous_iter_integral (μK := μK) (μ := μ)
    (fun (k : K) l y => e (G.M.co.rho B.ψ (shiftA H H' l) (om (g.1 * k.1, 1) Ψ₁)) y * ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)))
    (fun k l => ?_) (fun l y => ?_) (fun k y => ?_) (fun y₀ => ?_)
  · exact (GlobalTheory.ThKOp.continuous_of_mem_schA (hD _ l)).mul continuous_const
  · have h := GlobalTheory.T.evaluation_triple_period_case_a_second hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Ψ₁ hΨ₁m (shiftA H H' l) y
    exact (h.comp ((continuous_const.mul (continuous_subtype_val)).prodMk continuous_const)).mul continuous_const
  · have h := GlobalTheory.T.evaluation_triple_period_case_a_third hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ (om (g.1 * k.1, 1) Ψ₁) (hsp.pres (g.1 * k.1, 1) Ψ₁ hΨ₁m) y
    exact (h.mul (hν.mul hab)).aestronglyMeasurable
  · have hC' : IsCompact ((fun k : K => g.1 * k.1) '' Set.univ) :=
      isCompact_univ.image (continuous_const.mul continuous_subtype_val)
    obtain ⟨U, hU, Gf, hGf, hb⟩ := GlobalTheory.T.evaluation_triple_period_case_a_fourth hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ μ hμ Ψ₁ hΨ₁m _ hC' y₀
    refine ⟨U, hU, Gf, hGf, fun k l y hy => ?_⟩
    have := hb (g.1 * k.1) ⟨k, Set.mem_univ _, rfl⟩ l y hy
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    exact this

end GlobalTheory.ThKOpCont

end
