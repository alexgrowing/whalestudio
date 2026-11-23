import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.HoweLocal.LocUnitNonsplit

variable {F : Type} [Field F] [NumberField F]

theorem lintegral_eq_of_acts {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (hT : ∀ ν : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂ν)
    {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hφ₁ : φ₁ ∈ SB (κ → Fv F v))
    (hact : Acts (evFin F v) T φ φ₁)
    (μ : @Measure (κ → Fv F v) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let ev : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevc : Continuous ev :=
    continuous_pi fun i => (GlobalTheory.LatAtClosed.continuous_evFin' v).comp (continuous_apply i)
  have hevm : Measurable ev := hevc.measurable
  let φ₀ : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1
  have hφ₀ : φ₀ ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ 0 = 1 := by
    show Set.indicator _ 1 0 = 1
    rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from
      fun k => zero_mem _)]
    rfl
  let lift : (κ → Fv F v) → (κ → AF F) := fun a i => GlobalTheory.LatVac.liftV v (a i)
  have hlc : Continuous lift :=
    continuous_pi fun i => (GlobalTheory.LatAtClosed.continuous_liftV v).comp (continuous_apply i)
  have hat : ∀ a, At (evFin F v) (lift a) := fun a u hu => by
    funext i; exact GlobalTheory.LatVac.at_liftV v (a i) u hu
  have hevl : ∀ a, ev (lift a) = a := fun a => by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (a i)
  have hev_add : ∀ x y, ev (x + y) = ev x + ev y := fun x y => by
    funext i; exact map_add (evFin F v) (x i) (y i)

  have hRc : Continuous R := by
    have e : R = fun x => tens (evFin F v) φ₀ R (x - lift (ev x)) := by
      funext x
      have h1 : R (x - lift (ev x)) = R x := by
        rw [sub_eq_add_neg]
        refine (hR φ₀ hφ₀).1 x _ ?_
        intro u hu
        rw [smul_neg, hat (ev x) u hu, neg_zero]
      have h2 : (fun i => evFin F v ((x - lift (ev x)) i)) = 0 := by
        funext i
        show evFin F v (x i - GlobalTheory.LatVac.liftV v (evFin F v (x i))) = 0
        rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self]
      show R x = φ₀ (fun i => evFin F v ((x - lift (ev x)) i)) * R (x - lift (ev x))
      rw [h2, hφ₀0, one_mul, h1]
    rw [e]
    exact (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hR φ₀ hφ₀).2).comp
      (continuous_id.sub (hlc.comp hevc))
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → AF F), ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let d : (κ → AF F) → ENNReal := fun x => ‖R x‖ₑ ^ 2
  have hd : Measurable d := hRc.measurable.enorm.pow_const 2
  let m : Measure (κ → Fv F v) := (ν.withDensity d).map ev
  have hmint : ∀ f : (κ → Fv F v) → ENNReal, Measurable f → ∫⁻ y, f y ∂m = ∫⁻ x, d x * f (ev x) ∂ν := by
    intro f hf
    rw [lintegral_map hf hevm]
    exact lintegral_withDensity_eq_lintegral_mul ν hd (hf.comp hevm)
  have hsq : ∀ ψ' ∈ SB (κ → Fv F v), ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂m = ∫⁻ x, ‖tens (evFin F v) ψ' R x‖ₑ ^ 2 ∂ν := by
    intro ψ' hψ'
    rw [hmint _ (hψ'.1.continuous.measurable.enorm.pow_const 2)]
    congr 1
    funext x
    simp only [tens, d, ev, enorm_mul, mul_pow]
    ring

  haveI hinv : m.IsAddLeftInvariant := by
    constructor
    intro a
    ext s hs
    rw [Measure.map_apply (measurable_const_add a) hs]
    have hs' : MeasurableSet ((fun y => a + y) ⁻¹' s) := measurable_const_add a hs
    rw [← lintegral_indicator_one hs', ← lintegral_indicator_one hs, hmint _ (measurable_one.indicator hs'),
      hmint _ (measurable_one.indicator hs)]
    refine Eq.trans ?_ (lintegral_add_right_eq_self (fun x => d x * s.indicator 1 (ev x)) (lift a))
    congr 1
    funext x
    have e1 : d (x + lift a) = d x := by
      show ‖R (x + lift a)‖ₑ ^ 2 = ‖R x‖ₑ ^ 2
      rw [(hR φ₀ hφ₀).1 x _ (hat a)]
    have e2 : ev (x + lift a) = a + ev x := by rw [hev_add, hevl, add_comm]
    show d x * ((fun y => a + y) ⁻¹' s).indicator 1 (ev x) = d (x + lift a) * s.indicator 1 (ev (x + lift a))
    rw [e1, e2]
    rfl

  let U : Set (κ → Fv F v) := φ₀ ⁻¹' {1}
  have hUo : IsOpen U := hφ₀.1.isOpen_fiber 1
  have hU0 : (0 : κ → Fv F v) ∈ U := hφ₀0
  have hUm : m U < ⊤ := by
    calc m U = ∫⁻ y, U.indicator 1 y ∂m := (lintegral_indicator_one hUo.measurableSet).symm
    _ ≤ ∫⁻ y, ‖φ₀ y‖ₑ ^ 2 ∂m := lintegral_mono fun y => by
        by_cases hy : y ∈ U
        · rw [Set.indicator_of_mem hy]
          have h1 : φ₀ y = 1 := hy
          rw [h1]; simp
        · simp [hy]
    _ = ∫⁻ x, ‖tens (evFin F v) φ₀ R x‖ₑ ^ 2 ∂ν := hsq φ₀ hφ₀
    _ < ⊤ := by
        have hL := GlobalTheory.TorusDilate.memLp_of_mem_schA ν hν (hR φ₀ hφ₀).2
        have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hL.eLpNorm_lt_top
        simpa using h2
  haveI : IsLocallyFiniteMeasure m := ⟨fun y => ⟨(fun z => -y + z) ⁻¹' U,
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hU0)),
    by rw [measure_preimage_add]; exact hUm⟩⟩

  let c := m.addHaarScalarFactor μ
  have hmc : ∀ ψ' ∈ SB (κ → Fv F v), ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂m = c * ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂μ := by
    intro ψ' hψ'
    have hc : Continuous fun y => ‖ψ' y‖ ^ 2 := hψ'.1.continuous.norm.pow 2
    have hcs : HasCompactSupport fun y => ‖ψ' y‖ ^ 2 :=
      hψ'.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have key := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport m μ hc hcs
    have conv : ∀ ρ : Measure (κ → Fv F v), IsFiniteMeasureOnCompacts ρ →
        ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂ρ = ENNReal.ofReal (∫ y, ‖ψ' y‖ ^ 2 ∂ρ) := by
      intro ρ _
      rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
        (Filter.Eventually.of_forall fun _ => by positivity)]
      congr 1
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [conv m inferInstance, key, ← conv _ inferInstance, lintegral_smul_measure]
    rfl
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    have h1 := hmc φ₀ hφ₀
    rw [h0, zero_mul, hsq φ₀ hφ₀] at h1
    refine GlobalTheory.TorusDilate.lintegral_sq_ne_zero ν hν
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hR φ₀ hφ₀).2) ?_ h1
    show φ₀ (fun i => evFin F v ((0 : κ → AF F) i)) * R 0 ≠ 0
    have h2 : (fun i => evFin F v ((0 : κ → AF F) i)) = 0 := by funext i; exact map_zero _
    rw [h2, hφ₀0, one_mul]
    exact hR0
  have hU := hT ν hν _ (hR φ hφ).2
  rw [hact R (hR φ hφ)] at hU
  have hmm : ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂m = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂m := by rw [hsq φ₁ hφ₁, hsq φ hφ, hU]
  rw [hmc φ₁ hφ₁, hmc φ hφ] at hmm
  exact (ENNReal.mul_right_inj hc0 ENNReal.coe_ne_top).1 hmm

end GlobalTheory.HoweLocal.LocUnitNonsplit

open GlobalTheory.HoweLocal.LocUnitNonsplit in

theorem GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    IsUnitaryOn (sbClass (Fv F v)) omL := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB hstd hsplit v hv _ eB hcomp omL hL co hco
  intro μ hμ g φ hφ
  exact lintegral_eq_of_acts v (omB (eB.symm g).1) (fun ν hν Φ hΦ => hsplit.unit ν hν _ Φ hΦ) hφ (hL g φ hφ).1
    (hL g φ hφ).2 μ hμ
