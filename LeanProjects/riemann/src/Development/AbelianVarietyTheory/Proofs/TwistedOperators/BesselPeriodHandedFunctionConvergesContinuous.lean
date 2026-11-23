import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidDecRTrans
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPairedKernelFlatMapWeilTranslateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPairedKernelHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatKernelPairingRationalPointsInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.JacMean

theorem handP_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ B.L Φ₀ →
    IsThetaFunO ψ J.W B.V Φ →
    (∃ (C : ℝ) (a : ℕ), ∀ h h₁, ‖handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁‖ ≤ C * (quotHeight B.A h₁ * height B.V h) ^ a) ∧
    Continuous fun q : GA D B.V × GA D B.A => handP s vL omz φ Φ₀ (flFB s (s.om (1, q.1) Φ)) q.2 := by
  intro D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  have hfin : J.v0.μ J.v0.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨K, hK⟩ : ∃ K : GA D B.V → GA D J.W₀ → GA D B.A → ℂ, K = fun h h₀ h₁ => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := ⟨_, rfl⟩
  have hKc : Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => K q.1 q.2.1 q.2.2 := by
    subst hK; exact GlobalTheory.T.continuous_pairedKernel_flatMap_weilTranslate D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨C, a, hKp⟩ : ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
    subst hK; exact GlobalTheory.T.fourierJacobiToBessel_pairedKernel_heightBound D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKi : ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, K h (γ * h₀) h₁ = K h h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, K h h₀ (γ * h₁) = K h h₀ h₁ := by
    subst hK; exact GlobalTheory.T.flatKernelPairing_rationalPoints_invariant D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKq : ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ |C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a := by
    intro h h₀ h₁
    obtain ⟨γ, hγ, e1⟩ := exists_height_le_two_mul_quotHeight J.W₀ h₀
    obtain ⟨δ, hδ, e2⟩ := exists_height_le_two_mul_quotHeight B.A h₁
    have k1 : K h h₀ h₁ = K h (γ * h₀) (δ * h₁) := by
      rw [(hKi h).2 δ hδ (γ * h₀) h₁, (hKi h).1 γ hγ h₀ h₁]
    rw [k1]
    have p1 := height_pos J.W₀ (γ * h₀)
    have p2 := height_pos B.A (δ * h₁)
    have p3 := height_pos B.V h
    have q0 := quotHeight_pos J.W₀ h₀
    have q1 := quotHeight_pos B.A h₁
    calc ‖K h (γ * h₀) (δ * h₁)‖ ≤ C * (height J.W₀ (γ * h₀) * height B.A (δ * h₁) * height B.V h) ^ a := hKp _ _ _
      _ ≤ |C| * ((2 * quotHeight J.W₀ h₀) * (2 * quotHeight B.A h₁) * height B.V h) ^ a :=
          mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (mul_pos (mul_pos p1 p2) p3).le
            (mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 p2.le (by linarith)) p3.le) a)
            (pow_pos (mul_pos (mul_pos (by linarith) (by linarith)) p3) a).le (abs_nonneg C)
      _ = _ := by
          rw [show 2 * quotHeight J.W₀ h₀ * (2 * quotHeight B.A h₁) * height B.V h =
            4 * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) by ring, mul_pow]; ring
  obtain ⟨Cφ, hCφ⟩ := hφ.decay a
  have hpt : ∀ h h₀ h₁, ‖φ h₀ * K h h₀ h₁‖ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
    intro h h₀ h₁
    rw [norm_mul]
    calc ‖φ h₀‖ * ‖K h h₀ h₁‖ ≤ ‖φ h₀‖ * (|C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a) :=
          mul_le_mul_of_nonneg_left (hKq h h₀ h₁) (norm_nonneg _)
      _ = (‖φ h₀‖ * quotHeight J.W₀ h₀ ^ a) * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
          rw [mul_pow]; ring
      _ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((hCφ h₀).trans (le_abs_self _)) (by positivity))
            (pow_pos (mul_pos (quotHeight_pos B.A h₁) (height_pos B.V h)) a).le
  have hPeq : ∀ h h₁, handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ = ∫ h₀ in J.v0.𝓕, φ h₀ * K h h₀ h₁ ∂J.v0.μ := by
    subst hK; intro _ _; rfl
  refine ⟨⟨|Cφ| * (|C| * 4 ^ a) * (J.v0.μ J.v0.𝓕).toReal, a, fun h h₁ => ?_⟩, ?_⟩
  · rw [hPeq]
    have := norm_setIntegral_le_of_norm_le_const hfin fun h₀ _ => hpt h h₀ h₁
    refine this.trans (le_of_eq ?_)
    simp only [Measure.real]
    ring
  · have hmeas : ∀ q : GA D B.V × GA D B.A, AEStronglyMeasurable (fun h₀ => φ h₀ * K q.1 h₀ q.2) (J.v0.μ.restrict J.v0.𝓕) :=
      fun q => (hφ.continuous.mul (hKc.comp ((continuous_const.prodMk (continuous_id.prodMk continuous_const))))).aestronglyMeasurable
    have hc2 : Continuous fun q : GA D B.V × GA D B.A => (height B.A q.2 * height B.V q.1) ^ a :=
      (((continuous_height B.A).comp continuous_snd).mul ((continuous_height B.V).comp continuous_fst)).pow a
    refine (continuous_congr fun q : GA D B.V × GA D B.A => hPeq q.1 q.2).2 ?_
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    refine continuousAt_of_dominated (bound := fun _ => |Cφ| * (|C| * 4 ^ a) * ((height B.A q₀.2 * height B.V q₀.1) ^ a + 1))
      (.of_forall hmeas) ?_ (integrable_const _) ?_
    · filter_upwards [hc2.continuousAt.eventually (gt_mem_nhds (lt_add_one _))] with q hq
      refine .of_forall fun h₀ => (hpt q.1 h₀ q.2).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact (pow_le_pow_left₀ (mul_pos (quotHeight_pos B.A q.2) (height_pos B.V q.1)).le
        (mul_le_mul_of_nonneg_right (quotHeight_le_height B.A q.2) (height_pos B.V q.1).le) a).trans hq.le
    · exact .of_forall fun h₀ => (continuous_const.mul (hKc.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))).continuousAt

theorem conclusion₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → (∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G))) ∧ Continuous fun h => B.per ψ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ Φ hφ hG hΦ₀ hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨⟨C, a, hP⟩, hPc⟩ := handP_law D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  set P : GA D B.V → GA D B.A → ℂ := fun h h₁ => handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ with hPdef
  obtain ⟨C1, a1, h1⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D B.V B.V₀ σ B.d
  obtain ⟨C2, a2, h2⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
  obtain ⟨C3, h3⟩ := (GlobalTheory.RTransDecay.rapidDec_rTrans D B.V G hG).2 (a1 * a2 * a)

  set bd : GA D B.V → ℝ := fun h => |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (|C3| * height B.V h ^ (a1 * a2 * a))) with hbd
  have hbound : ∀ h (h₁ : GA D B.A) (n : flagN B.d), ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ ≤ bd h := by
    intro h h₁ n
    have hg := h1 n.1 n.2 (B.o.emb (h₁, 1))
    have hq := (h2 h₁).1
    set g : GA D B.V := n.1 * embA B.d B.o h₁ with hgdef
    have hge : n.1 * B.d.emb0 (B.o.emb (h₁, 1)) = g := rfl
    rw [hge] at hg
    have q0 := quotHeight_pos B.V₀ (B.o.emb (h₁, 1))
    have qg := quotHeight_pos B.V g
    have qa := quotHeight_pos B.A h₁
    have ht := height_pos B.V h
    have hA : quotHeight B.A h₁ ≤ |C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2) := by
      calc quotHeight B.A h₁ ≤ C2 * quotHeight B.V₀ (B.o.emb (h₁, 1)) ^ a2 := hq
        _ ≤ |C2| * (|C1| * quotHeight B.V g ^ a1) ^ a2 :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ q0.le (hg.1.trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos qg a1).le)) _) (pow_pos q0 a2).le (abs_nonneg _)
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    have hGg := h3 g h
    have hPb := hP h h₁
    have hnpsi : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hψ.1.2.1 _
    have e1 : ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ = ‖P h h₁‖ * ‖G (g * h)‖ := by
      simp only [besFun, rTrans, norm_mul, norm_star, hnpsi, mul_one]; rfl
    rw [e1]
    calc ‖P h h₁‖ * ‖G (g * h)‖ ≤ (|C| * (quotHeight B.A h₁ * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (hPb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos (mul_pos qa ht) a).le)) (norm_nonneg _)
      _ ≤ (|C| * ((|C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2)) * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos qa ht).le
            (mul_le_mul_of_nonneg_right hA ht.le) a) (abs_nonneg C)) (norm_nonneg _)
      _ = |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (‖G (g * h)‖ * quotHeight B.V g ^ (a1 * a2 * a))) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ bd h :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGg.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos ht _).le)) (by positivity)) (mul_nonneg (abs_nonneg _) (pow_pos ht a).le)
  have hcont : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => besFun ψ 1 B.d B.o B.ζ (P q.1) (rTrans q.1 G) q.2.1 q.2.2 := by
    have hn : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => (q.2.2 : GA D B.V) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((hPc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
      (hG.continuous.comp ((hn.mul (B.d.continuous_embed.comp (B.o.continuous_emb.comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)))).mul continuous_fst))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))
  have hint : ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) := by
    intro h
    refine Integrable.of_bound ?_ (bd h) (.of_forall fun p => hbound h p.1 p.2)
    exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have heq : ∀ h, B.per ψ (P h) (rTrans h G) = ∫ p, Function.uncurry (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) p
      ∂((B.vA.μ.restrict B.vA.𝓕).prod (B.vN.ν.restrict B.vN.𝓝)) := fun h => by
    rw [integral_prod _ (hint h)]; rfl
  refine (continuous_congr heq).2 ?_
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  have hbc : Continuous bd := by
    exact (continuous_const.mul ((continuous_height B.V).pow a)).mul (continuous_const.mul (continuous_const.mul ((continuous_height B.V).pow _)))
  refine continuousAt_of_dominated (bound := fun _ => bd h₀ + 1) ?_ ?_ (integrable_const _) ?_
  · exact .of_forall fun h => (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hbc.continuousAt.eventually (gt_mem_nhds (lt_add_one (bd h₀)))] with h hh
    exact .of_forall fun p => (hbound h p.1 p.2).trans hh.le
  · exact .of_forall fun p => (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

end GlobalTheory.JacMean
