import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LiftTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem tame_congr (hψ : IsStdChar D ψ (-1)) {ℓ ℓ' : (WO S T → ℂ) → ℂ} (h : Tame ψ S T ℓ)
    (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simpa only [hh f hf] using h.cont f hf
  · simpa only [hh f hf] using h.bdd f hf
  · rw [e _ hI, h.sup f hf m α hα hI]
    simp only [hh f hf]

theorem finite_vol {V : HSp D} (v : GlobalTheory.Unf.Vol V) : IsFiniteMeasure (v.μ.restrict v.𝓕) := by
  have h : IntegrableOn (fun _ => (1 : ℝ)) v.𝓕 v.μ := by
    simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 v.haar v.fund
  rcases (integrableOn_const_iff (by simp)).1 h with h | h
  · simp at h
  · exact isFiniteMeasure_restrict.2 h.ne

theorem tame_double {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) (vT : GlobalTheory.Unf.Vol T)
    {G : GA D T → ℂ} (hG : RapidDec T G) {A : HSp D} (vA : GlobalTheory.Unf.Vol A) {φ : GA D A → ℂ} (hφ : RapidDec A φ)
    {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N)
    [IsFiniteMeasure ν] (K : GA D A → N → ℂ) (g : GA D A → N → GA D S)
    (hK : Continuous fun p : GA D A × N => K p.1 p.2) (hg : Continuous fun p : GA D A × N => g p.1 p.2)
    {C C' : ℝ} {a a' : ℕ} (hKb : ∀ h n, ‖K h n‖ ≤ C * (‖φ h‖ * quotHeight A h ^ a))
    (hgb : ∀ h n, quotHeight S (g h n) ≤ C' * quotHeight A h ^ a') :
    Tame ψ S T fun Φ => ∫ h in vA.𝓕, ∫ n, K h n * liftS om vT.μ vT.𝓕 G Φ (g h n) ∂ν ∂vA.μ := by
  obtain ⟨-, h2A, -, hbA, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, h2T, -, hbT, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  haveI := finite_vol vA
  haveI := finite_vol vT
  have hc : Continuous fun y : (GA D A × N) × GA D T => K y.1.1 y.1.2 * G y.2 :=
    (hK.comp continuous_fst).mul (hG.continuous.comp continuous_snd)
  have hg' : Continuous fun y : (GA D A × N) × GA D T => g y.1.1 y.1.2 := hg.comp continuous_fst
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ S T χS χT om hom ((GA D A × N) × GA D T)
    (((vA.μ.restrict vA.𝓕).prod ν).prod (vT.μ.restrict vT.𝓕)) (fun y => K y.1.1 y.1.2 * G y.2) (fun y => g y.1.1 y.1.2)
    (fun y => y.2) (fun _ => 0) hc.measurable hg' continuous_snd continuous_const (fun k => by
      obtain ⟨M, hM⟩ := hφ.decay (a + a' * k)
      obtain ⟨M', hM'⟩ := hG.decay k
      refine Integrable.of_bound (hc.norm.mul ((((continuous_quotHeight S).comp hg').mul
        ((continuous_quotHeight T).comp continuous_snd)).pow k)).aestronglyMeasurable (|C| * |C'| ^ k * M * M')
        (Filter.Eventually.of_forall fun y => ?_)
      obtain ⟨⟨h, n⟩, t⟩ := y
      have p1 := (quotHeight_pos A h).le
      have p2 := (quotHeight_pos T t).le
      have p3 := (quotHeight_pos S (g h n)).le
      have b1 : ‖K h n‖ ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) :=
        (hKb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      have b2 : quotHeight S (g h n) ≤ |C'| * quotHeight A h ^ a' :=
        (hgb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
      have hM0 : 0 ≤ M := le_trans (by positivity) (hM h)
      show ‖‖K h n * G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖K h n‖ * ‖G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k
          ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) * ‖G t‖ * (|C'| * quotHeight A h ^ a' * quotHeight T t) ^ k := by gcongr
        _ = |C| * |C'| ^ k * (‖φ h‖ * quotHeight A h ^ (a + a' * k)) * (‖G t‖ * quotHeight T t ^ k) := by ring
        _ ≤ _ := by gcongr; exacts [hM h, hM' t])
  refine tame_congr hom.std hT fun f hf => ?_
  have h1 := hI f hf
  rw [integral_prod _ h1, integral_prod _ h1.integral_prod_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [liftS_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring

theorem lift_periods_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  intro D ψ W vW G hG
  refine ⟨fun ρ B χ χ' om hom φ hφ => ?_, fun ρ J χ χ' om hom L' ζ' χ₁ χ₂ omz homz φ Φ₀ hφ hΦ₀ => ?_⟩
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
    haveI : SecondCountableTopology (flagN B.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN B.d : Set (GA D B.V))
    haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D B.V B.V₀ ρ B.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
    have hn : Continuous fun p : GA D B.A × flagN B.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have := tame_double hom vW hG B.vA hφ (B.vN.ν.restrict B.vN.𝓝)
      (fun h (n : flagN B.d) => φ h * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)) (fun h n => n.1 * embA B.d B.o h)
      ((hφ.continuous.comp continuous_fst).mul
        ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hom.std.1.1 1 (vecB B.o B.ζ)).comp hn).star)
      (hn.mul ((B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))).comp
        continuous_fst))
      (C := 1) (a := 0) (C' := |C₁| * |C₂| ^ a₁) (a' := a₂ * a₁) (fun h n => by
        have e : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hom.std.1.2.1 _
        simp [e]) (fun h n => by
        have p1 := (quotHeight_pos B.A h).le
        have p2 := (quotHeight_pos B.V₀ (B.o.emb (h, 1))).le
        have b : quotHeight B.V₀ (B.o.emb (h, 1)) ≤ |C₂| * quotHeight B.A h ^ a₂ :=
          (h₂ h).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        calc _ ≤ C₁ * quotHeight B.V₀ (B.o.emb (h, 1)) ^ a₁ := (h₁ n.1 n.2 _).2
          _ ≤ |C₁| * (|C₂| * quotHeight B.A h ^ a₂) ^ a₁ := by gcongr; exact le_abs_self _
          _ = _ := by ring)
    convert this using 2 with Φ
    unfold BesL.per besPer besFun
    congr 1; funext h; congr 1; funext n; ring
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
    haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN J.d : Set (GA D J.W))
    haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hn : Continuous fun p : GA D J.W₀ × flagN J.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have hth : ∀ n h, thetaJS ψ J.d ζ' omz Φ₀ n h =
        ψ (cenS J.d L' (zEll L' ρ ζ') n) * omz (h, 1) Φ₀ (ptS J.d L' (zEll L' ρ ζ') n) := fun n h => by
      rw [thetaJS, GlobalTheory.Unf.FB.ThLaws.jacS_zero_apply]
    have hJ : Continuous fun p : (GA D J.W₀ × GA D L') × WO J.W₀ L' => omz p.1 Φ₀ p.2 :=
      (@GlobalTheory.Unf.jointCont_all D) ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hthc : Continuous fun p : GA D J.W₀ × flagN J.d => thetaJS ψ J.d ζ' omz Φ₀ p.2.1 p.1 := by
      simp only [hth]
      exact (hom.std.1.1.comp ((GlobalTheory.Unf.FB.ThLaws.continuous_cenS _ _ _).comp hn)).mul
        (hJ.comp ((continuous_fst.prodMk continuous_const).prodMk ((GlobalTheory.Unf.FB.ThLaws.continuous_ptS _ _ _).comp hn)))
    have := tame_double hom vW hG J.v0 hφ (J.vN.ν.restrict J.vN.𝓝)
      (fun h (n : flagN J.d) => φ h * star (thetaJS ψ J.d ζ' omz Φ₀ n.1 h) * star (psiFlag ψ J.d n.1))
      (fun h n => n.1 * J.d.emb0 h)
      (((hφ.continuous.comp continuous_fst).mul hthc.star).mul
        ((GlobalTheory.Unf.FB.ThLaws.continuous_psiFlag hom.std.1.1 _).comp hn).star)
      (hn.mul (J.d.continuous_embed.comp continuous_fst))
      (C := C₂ * quotHeight L' 1 ^ a₂) (a := a₂) (C' := C₁) (a' := a₁) (fun h n => by
        have e : ‖psiFlag ψ J.d n.1‖ = 1 := hom.std.1.2.1 _
        rw [norm_mul, norm_mul, norm_star, norm_star, e, hth, norm_mul, hom.std.1.2.1, one_mul, mul_one]
        refine (mul_le_mul_of_nonneg_left (h₂ h 1 _) (norm_nonneg _)).trans (le_of_eq ?_)
        ring) (fun h n => (h₁ n.1 n.2 _).2)
    convert this using 2 with Φ
    unfold JacL.per fjSrc fjSrcFun
    congr 1; funext h; congr 1; funext n; ring

end GlobalTheory.LiftTame

end
