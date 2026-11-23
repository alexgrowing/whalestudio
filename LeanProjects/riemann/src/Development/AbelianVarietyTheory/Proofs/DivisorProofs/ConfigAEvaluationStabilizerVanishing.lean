import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigASchwartzEvalCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigASchwartzEvalEqualStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeMeas

set_option maxHeartbeats 800000

theorem coneIntegrand_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
      ∀ μY : Measure (Fin b × Fin (b + a') → AF F), μY.IsAddHaarMeasure →
      AEStronglyMeasurable (fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) => e (G.M.co.rho B.ψ (shiftA H H' p.2.1) (om (p.1.1, 1) Ψ)) p.2.2 * (X.ν p.2.1 : ℂ) *
          ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) (μK.prod (μ.prod μY)) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ μY _
  set mY : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _ with hmY
  haveI : BorelSpace (Fin b × Fin (b + a') → AF F) := ⟨rfl⟩

  have hk : ∀ (l : (AE F E)ˣ) (y : Fin b × Fin (b + a') → AF F),
      Continuous fun g : UA σ G.V.J => e (G.M.co.rho B.ψ (shiftA H H' l) (om (g, 1) Ψ)) y :=
    fun l y => GlobalTheory.T.config_A_schwartz_eval_compare F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Ψ hΨ l y
  have hl : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ y : Fin b × Fin (b + a') → AF F,
      Measurable fun l : (AE F E)ˣ => e (G.M.co.rho B.ψ (shiftA H H' l) Φ) y :=
    fun Φ hΦ y => GlobalTheory.T.config_A_schwartz_eval_equal F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ y
  have hmem : ∀ g : UA σ G.V.J, om (g, 1) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := fun g =>
    (IsUWeilPair.isUSplitting hT.weil).pres (g, 1) Ψ hΨ
  have hy : ∀ (g : UA σ G.V.J) (l : (AE F E)ˣ),
      Continuous fun y => e (G.M.co.rho B.ψ (shiftA H H' l) (om (g, 1) Ψ)) y := fun g l =>
    GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F
      (he.maps _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hT.base.std _ _ (hmem g)))

  obtain ⟨hTG, -, hSCU, hT2U⟩ := GlobalTheory.LeviModulus.topUA σ G.V.J
  haveI := hTG; haveI := hSCU; haveI := hT2U
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : SecondCountableTopology K := inferInstance
  haveI : IsTopologicalGroup K := inferInstance
  haveI : T2Space K := inferInstance
  haveI : RegularSpace K := IsTopologicalGroup.regularSpace _
  haveI : T1Space K := T2Space.t1Space
  haveI : T0Space K := T1Space.t0Space
  haveI : T3Space K := T3Space.mk
  haveI : TopologicalSpace.MetrizableSpace K := TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : OpensMeasurableSpace K := inferInstance
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : RegularSpace (AF F) := IsTopologicalAddGroup.regularSpace _
  haveI : T1Space (AF F) := T2Space.t1Space
  haveI : T0Space (AF F) := T1Space.t0Space
  haveI : T3Space (AF F) := T3Space.mk
  haveI : TopologicalSpace.MetrizableSpace (AF F) := TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : TopologicalSpace.MetrizableSpace (Fin b × Fin (b + a') → AF F) := inferInstance
  haveI : SecondCountableTopology (Fin b × Fin (b + a') → AF F) := inferInstance

  have hin : ∀ k : K, Measurable fun p : (AE F E)ˣ × (Fin b × Fin (b + a') → AF F) =>
      e (G.M.co.rho B.ψ (shiftA H H' p.1) (om (k.1, 1) Ψ)) p.2 := by
    intro k
    let u : (Fin b × Fin (b + a') → AF F) → (AE F E)ˣ → ℂ := fun y l =>
      e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y
    have h1 : ∀ l, Continuous fun y => u y l := fun l => hy k.1 l
    have h2 : ∀ y, Measurable (u y) := fun y => hl _ (hmem k.1) y
    have h : Measurable (Function.uncurry u) :=
      @measurable_uncurry_of_continuous_of_measurable _ ℂ (Fin b × Fin (b + a') → AF F) _ _ mY _ _ _ _ _ _ _ u h1 h2
    have h3 := h.comp (measurable_swap (α := (AE F E)ˣ) (β := Fin b × Fin (b + a') → AF F))
    exact h3
  have hout : StronglyMeasurable fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) =>
      e (G.M.co.rho B.ψ (shiftA H H' p.2.1) (om (p.1.1, 1) Ψ)) p.2.2 :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (k : K) (p : (AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) =>
        e (G.M.co.rho B.ψ (shiftA H H' p.1) (om (k.1, 1) Ψ)) p.2)
      (fun p => (hk p.1 p.2).comp continuous_subtype_val) (fun k => (hin k).stronglyMeasurable)
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  have hν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) := by
    have h1 := hT.chars.heckeα.1
    have h2 := hT.chars.heckeβ.1
    have : (fun l : (AE F E)ˣ => (X.ν l : ℂ)) = fun l => ((X.α l : ℂ) / (X.β l : ℂ)) := by
      funext l; simp [Chars.ν]
    rw [this]
    exact (continuous_subtype_val.comp h1).div (continuous_subtype_val.comp h2) (fun l => by simp)
  have hm : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) :=
    hν.mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE (F := F) (E := E)))).pow _)
  have hm' : StronglyMeasurable fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) =>
      (X.ν p.2.1 : ℂ) * ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) :=
    (hm.measurable.comp (measurable_fst.comp measurable_snd)).stronglyMeasurable
  have := hout.mul hm'
  refine this.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.mul_apply]
  ring

end GlobalTheory.ConeMeas
