import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ExtContRep

theorem comp_rep_ae_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Set G) (hΓ : Γ.Countable) (D : Set G) (hD : MeasurableSet D)
    (r : G → G) (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ r y ∈ D) (F f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (h : F =ᵐ[μ.restrict D] f) :
    (fun y => F (r y)) =ᵐ[μ] f := by
  have h1 : ∀ᵐ x ∂μ, x ∈ D → F x = f x := (ae_restrict_iff' hD).1 h
  have h2 : ∀ᵐ x ∂μ, ∀ γ ∈ Γ, γ * x ∈ D → F (γ * x) = f (γ * x) :=
    (ae_ball_iff hΓ).2 fun γ _ => (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with x hx
  obtain ⟨γ, hγ, e, hm⟩ := hr x
  rw [e] at hm ⊢
  rw [hx γ hγ hm, hf γ hγ]

theorem ae_ae_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [SFinite μ] [SFinite ν] (p : G → Prop) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, p (m * x) := by
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h0 : ∀ᵐ x ∂μ, x ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  have hm : MeasurableSet {z : G × G | z.2 * z.1 ∉ Z} :=
    (measurable_snd.mul measurable_fst) hZm.compl
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z :=
    (Measure.ae_ae_comm (p := fun x m => m * x ∉ Z) hm).2
      (Filter.Eventually.of_forall fun m =>
        (measurePreserving_mul_left μ m).quasiMeasurePreserving.ae h0)
  filter_upwards [h1] with x hx
  filter_upwards [hx] with m hmx
  by_contra hp
  exact hmx (hZ hp)

theorem ext_ae_eq_contRep : ∀ (B : RowsAut) (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B y f → B.I.ext y =ᵐ[B.I.muA B.μf] f ∧ (∀ f', IsContRep B y f' → f' = f) ∧ (∀ g, IsContRep B (B.R g y) (fun x => f (x * g))) ∧ ∀ ν : Measure B.I.GA, IsFiniteMeasure ν → ∀ᵐ x ∂(B.I.muA B.μf), ∀ᵐ m ∂ν, B.I.ext y (m * x) = f (m * x) := by
  intro B y f hf
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓ, hc, -, -⟩ := GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hl, hrt, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : (B.I.muA B.μf).IsMulRightInvariant := ⟨hrt⟩
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  have : SFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hcount : B.I.GFset.Countable := by
    rw [← hΓ]; exact Set.countable_coe_iff.1 hc
  have hr : ∀ z, ∃ γ ∈ B.I.GFset, B.I.rep B.fund z = γ * z ∧ B.I.rep B.fund z ∈ B.fund := by
    intro z
    have h := B.fund_spec.2.1 z
    have e : B.I.rep B.fund z = h.choose * z := by
      unfold AutInst.rep; exact dif_pos h
    exact ⟨h.choose, h.choose_spec.1, e, e ▸ h.choose_spec.2⟩
  have key : ∀ f', IsContRep B y f' → B.I.ext y =ᵐ[B.I.muA B.μf] f' := fun f' hf' =>
    comp_rep_ae_eq (B.I.muA B.μf) _ hcount _ B.fund_spec.1 _ hr _ f' hf'.2.1 hf'.2.2
  refine ⟨key f hf, fun f' hf' => ?_, fun g => ⟨?_, ?_, ?_⟩, fun ν hν => ?_⟩
  · exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hf'.1 hf.1).1 ((key f' hf').symm.trans (key f hf))
  · exact hf.1.comp (continuous_id.mul continuous_const)
  · intro γ hγ x
    simp only [mul_assoc]
    exact hf.2.1 γ hγ _
  · refine (B.R_spec g y).trans (ae_restrict_of_ae ?_)
    exact (measurePreserving_mul_right (B.I.muA B.μf) g).quasiMeasurePreserving.ae (key f hf)
  · exact ae_ae_mul (B.I.muA B.μf) ν (fun x => B.I.ext y x = f x) (key f hf)

end GlobalTheory.ExtContRep
