import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffListProdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTwoLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetSmoothModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfIsSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentSiegelSetIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerDescentConvergentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleWittTowerDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerDescentPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryIffGroupPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AutomorphicArithmetic.DivisorFrames.ThetaInvariantUnderOpenSubgroup
import Development.AutomorphicArithmetic.DivisorFrames.ArchimedeanDiagonalMatrixExists
import Development.AutomorphicArithmetic.DivisorFrames.ThetaFunctionPolynomialGrowthBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar GlobalTheory.ThK.LiftConst

namespace GlobalTheory.ThK.LiftUnitV

open GlobalTheory.ThK.TowerInt GlobalTheory.ThK.SplitInv GlobalTheory.ThKLiftCusp GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.LiftUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

private theorem contMul_UA (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) : ContinuousMul (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  infer_instance

private theorem smoothMod_thLift (hK : KP) (hP : IsPair B M χX χW om r s r' s') {f : UA σ W.J → ℂ} (hfc : Continuous f)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) {μ : Measure (UA σ W.J)} {𝓕 : Set (UA σ W.J)} (hv : μ 𝓕 < ⊤)
    (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    GlobalTheory.SiegelSet.IsSmoothModerate σ (c • X.J.map σ) fun x => thLift om Φ μ 𝓕 f ((toGAd hσ X.J hc).symm x) := by
  haveI := contMul_UA σ X.J
  have hb := (GlobalTheory.T.theta_basic_properties hK.base F E σ B n d X W M χX χW om r s r' s' hP).1
  obtain ⟨N, hN⟩ := UpperTheory.theta_function_polynomial_growth_bound hK F E σ B n d X W M χX χW om r s r' s' hP
  have hreg := fun Ψ (hΨ : Ψ ∈ schA F (Fin n × Fin d)) => lift_reg hfc hdec hv N (hb Ψ hΨ).1 (hN Ψ hΨ)
  set e := toGAd hσ X.J hc
  have he : Continuous e.symm := continuous_subtype_val.subtype_mk _
  have hpres := (IsUWeilPair.isUSplitting hP.weil).pres
  obtain ⟨l, -, hl⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin d)
  obtain ⟨hsm, hfold⟩ := smooth_of_der hP.base.cm (c • X.J.map σ) (schA F (Fin n × Fin d))
    (fun Ψ x => thLift om Ψ μ 𝓕 f (e.symm x)) (fun Ψ hΨ => (hreg Ψ hΨ).2.1.comp he)
    (fun {ι} t a Ψ hΨ x => by
      have hs : ∑ i ∈ t, (a i : ℂ) • Ψ i ∈ schA F (Fin n × Fin d) :=
        Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hΨ i hi)
      simp only [thLift_def, ← integral_const_mul]
      rw [← integral_finset_sum _ fun i hi => ((hreg _ (hΨ i hi)).1 _).const_mul _]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [theta]
      rw [← hl _ (hpres _ _ hs), map_sum, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_smul, map_smul, hl _ (hpres _ _ (hΨ i hi)), smul_eq_mul, map_mul, Complex.conj_ofReal]
      ring)
    (fun w τ => by
      obtain ⟨D, hD, hDd⟩ := UpperTheory.archimedean_diagonal_matrix_exists hK F E σ B n d X W M χX χW om r s r' s' hP hσ c hc w τ
      refine ⟨D, hD, fun Z γ hγ hadd h1 h2 Ψ hΨ x => ?_⟩
      simp only [map_mul]
      exact (hreg _ (hD Z Ψ hΨ)).2.2.2 (theta om Ψ) (fun t => e.symm (γ t)) (he.comp hγ)
        (fun a b => by rw [hadd, map_mul]) (hreg Ψ hΨ).1 (hDd Z γ h1 h2 Ψ hΨ) (e.symm x)) hΦ
  refine ⟨fun γ hγ g => ?_, ?_, (hreg Φ hΦ).2.1.comp he, hsm, N, fun l hl => ?_⟩
  · have hγ' : e.symm γ ∈ ratU σ X.J := (GlobalTheory.T.rational_unitary_iff_group_points F E σ hσ n X.J c hc _).2 (by rwa [MulEquiv.apply_symm_apply])
    simp only [thLift_def, map_mul]
    refine integral_congr_ae (.of_forall fun h => ?_)
    have := (hb Φ hΦ).2.1 _ hγ' 1 (one_mem _) (e.symm g) h
    rw [one_mul] at this
    simp only [this]
  · obtain ⟨U, hU, hfix⟩ := UpperTheory.theta_invariant_under_open_subgroup hK F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
    refine ⟨U.comap e.symm.toMonoidHom, hU.preimage he, fun k hk hfin g => ?_⟩
    have h1 : om (e.symm k, 1) Φ = Φ := hfix _ hk (congrArg Units.val (MonoidHom.mem_ker.1 hfin))
    simp only [thLift_def, map_mul, theta]
    refine integral_congr_ae (.of_forall fun h => ?_)
    beta_reduce
    rw [show ((e.symm g * e.symm k, h) : UA σ X.J × UA σ W.J) = (e.symm g, h) * (e.symm k, 1) by simp,
      map_mul, Module.End.mul_apply, h1]
  · obtain ⟨Ψ, hΨ, eq⟩ := hfold l hl
    obtain ⟨C, hC⟩ := (hreg Ψ hΨ).2.2.1
    exact ⟨C, fun g => by rw [eq]; exact hC _⟩

private theorem unitary_pair (hK : KP) {Y : Spc F E n} {Mo : Model σ Y W} {ω : Rep σ Y W}
    (hP : IsPair B Mo χX χW ω r s r' s') (hdet : W.J.det ≠ 0) {f : UA σ W.J → ℂ} (hfc : Continuous f)
    (hfl : ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C)
    (hcusp : ∃ (c₀ : E) (K : Subgroup (GAd σ (c₀ • W.J.map σ))) (φ : GAd σ (c₀ • W.J.map σ) → ℂ),
      IsHermND σ (c₀ • W.J.map σ) ∧ GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K ∧ GlobalTheory.UAut.IsAut σ (c₀ • W.J.map σ) K φ ∧
      GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • W.J.map σ) φ ∧
      ∀ (h : UA σ W.J) (h' : GAd σ (c₀ • W.J.map σ)), h.1 = h'.1 → φ h' = f h)
    (hlz : ∀ (n₁ k : ℕ) (JX : Matrix (Fin n₁) (Fin n₁) E), 1 ≤ k → n₁ + 2 * k = n → (∀ s t, σ (JX t s) = JX s t) →
      JX.det ≠ 0 → LiftZero B.ψ JX W.J χX χW f)
    {μ : Measure (UA σ W.J)} {𝓕 : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ)
    {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (v : Pl F) :
    Unitary (UAtSub σ Y (evFin F v)) (liftSpace ω Φ μ 𝓕 f v) := by
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c₀, hc₀, hc₀s⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ := GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hP.skew.skew hdet hc₀ hc₀s
  haveI := hμ
  have hv : μ 𝓕 < ⊤ := GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hK.siegelSetUnitary hcm hc₀ hJ h𝓕
  have hY := GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm
  have hY1 : IsHermND σ ((1 : E) • Y.J.map σ) := by rwa [one_smul]
  have hdY : Y.J.det ≠ 0 := fun h => hY.2 (by
    rw [show Y.J.map σ = (σ : E →+* E).mapMatrix Y.J from rfl, ← RingHom.map_det, h, map_zero])
  have hb := (GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ Y _ Mo _ _ ω r s r' s' hP).1
  have hpres := (IsUWeilPair.isUSplitting hP.weil).pres
  have key : ∀ Ψ ∈ schA F (Fin n × Fin d), Continuous (thLift ω Ψ μ 𝓕 f) ∧
      (∀ γ ∈ ratU σ Y.J, ∀ g, thLift ω Ψ μ 𝓕 f (γ * g) = thLift ω Ψ μ 𝓕 f g) ∧ ∃ C : ℝ, ∀ g, ‖thLift ω Ψ μ 𝓕 f g‖ ≤ C := by
    intro Ψ hΨ
    have hsm := smoothMod_thLift hK hP hfc hdec hv hσ one_ne_zero hΨ
    have hcu := hK.rallisTowerUnitary F E σ hcm B.ψ (GlobalTheory.StdCharFromIsStd.isCharAF hP.base.std) n d Y.J W.J hP.herm.herm hdY
      hP.skew.skew hdet χX χW hP.hX hP.hW hP.resX hP.resW f hcusp hlz Mo.co hP.good.rat ω hP.weil Ψ hΨ μ 𝓕 hμ h𝓕 1 hY1
      (fun x => thLift ω Ψ μ 𝓕 f ((toGAd hσ Y.J one_ne_zero).symm x))
      (fun g g' hg => congrArg (thLift ω Ψ μ 𝓕 f) (Subtype.ext hg.symm))
    obtain ⟨C, hC⟩ := GlobalTheory.SiegelSet.rapidDecay_qht hK.siegelSetUnitary F E σ hcm n Y.J 1 one_ne_zero hY1
      (thLift ω Ψ μ 𝓕 f) _ (fun g g' hg => congrArg (thLift ω Ψ μ 𝓕 f) (Subtype.ext hg.symm)) hsm hcu 0
    have he : Continuous (toGAd hσ Y.J (one_ne_zero (α := E))) := continuous_subtype_val.subtype_mk _
    have hcont : Continuous (thLift ω Ψ μ 𝓕 f) := by
      have h0 := hsm.cont.comp he
      convert h0 using 1
      funext g
      simp only [Function.comp_apply, MulEquiv.symm_apply_apply]
    refine ⟨hcont, fun γ hγ g => ?_, C, fun g => by simpa using hC g⟩
    simp only [thLift_def]
    refine integral_congr_ae (.of_forall fun h => ?_)
    have := (hb Ψ hΨ).2.1 _ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    simp only [this]
  haveI := contMul_UA σ Y.J
  haveI := hP.good.haar
  haveI := GlobalTheory.HermUnimod.isMulRightInvariant_of_isHerm F E σ B n Y r s hP.base hP.herm Mo.μ hP.good.haar
  have hr := GlobalTheory.SkewUnimod.isMulRightInvariant_of_isSkew F E σ B _ _ r' s' hP.base hP.skew μ hμ
  refine unitary_of_bounded Mo.μ hP.good.dom
    (GlobalTheory.UnitaryVol.measure_fundDom_lt_top hK.siegelSetUnitary hcm hY hP.good.dom) _ _ fun φ hφ => ?_
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨Ψ, ⟨k, -, h, -, Φ', hΦ', rfl⟩, f', ⟨h₁, -, rfl⟩, rfl⟩ := hφ
    have hΦ'' : Φ' ∈ schA F (Fin n × Fin d) := by
      rcases hΦ' with rfl | ⟨-, φ, φ', ρ, -, -, hρ, rfl⟩
      exacts [hΦ, hρ.2]
    have hS := hpres (1, h₁⁻¹) _ (hpres (k, h) _ hΦ'')
    have e : thLift ω (ω (k, h) Φ') μ 𝓕 (rt h₁ f) = thLift ω (ω (1, h₁⁻¹) (ω (k, h) Φ')) μ 𝓕 f :=
      funext (GlobalTheory.ThK.LiftConst.thLift_mul_right ω _ μ 𝓕 hμ hr h𝓕 f hfl h₁ fun γ hγ g x => by
        simpa using (hb _ hS).2.1 1 (one_mem _) γ hγ g x)
    rw [e]
    exact key _ hS
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl, 0, fun _ => by simp⟩
  | add φ ψ _ _ h1 h2 =>
    obtain ⟨a1, a2, C, a3⟩ := h1
    obtain ⟨b1, b2, C', b3⟩ := h2
    exact ⟨a1.add b1, fun γ hγ g => by simp only [Pi.add_apply, a2 γ hγ, b2 γ hγ], C + C',
      fun g => (norm_add_le _ _).trans (add_le_add (a3 g) (b3 g))⟩
  | smul t φ _ h1 =>
    obtain ⟨a1, a2, C, a3⟩ := h1
    exact ⟨a1.const_smul t, fun γ hγ g => by simp only [Pi.smul_apply, a2 γ hγ], ‖t‖ * C,
      fun g => by rw [Pi.smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left (a3 g) (norm_nonneg _)⟩
end GlobalTheory.ThK.LiftUnitV

open GlobalTheory.ThK.SplitInv
open GlobalTheory.ThK.TowerInt GlobalTheory.ThK.SquareIntegrability in
theorem _root_.GlobalTheory.T.matched_tower_adapted_planes_second : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
      ∀ i < G.p, ∀ f ∈ Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i, IsCT (W := sp i) (pl i) f 0 → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F (sp i).J)) (Fin a' × Fin (d₁ - 2 * i)),
        (∀ x : Matrix (Fin a') (Fin (d₁ - 2 * i)) E, ∃ y z : Fin a' × Fin (d₁ - 2 * i) → F,
          co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
      ∀ om₁ : UA σ G.V'.J × UA σ (sp i).J →* Module.End ℂ ((Fin a' × Fin (d₁ - 2 * i) → AF F) → ℂ),
        IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F (sp i).J) co X.α (X.α / X.β) om₁ →
      ∀ Φ ∈ schA F (Fin a' × Fin (d₁ - 2 * i)), ∀ (μ : Measure (UA σ (sp i).J)) (𝓕 : Set (UA σ (sp i).J)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ (sp i).J) 𝓕 μ →
      ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T → SplitsFully E v → Unitary (UAtSub σ G.V' (evFin F v)) (liftSpace (X := G.V') (W := sp i) om₁ Φ μ 𝓕 f v) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH' hiso c hb0 hbj i hi f hf hct hdec
    co hco om₁ hom Φ hΦ μ 𝓕 hμ h𝓕
  have hsm := GlobalTheory.T.theta_tower_descent_period hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH' hiso c hb0 hbj i hi f hf hct hdec
  have hT := hM.triple
  have hB := hT.base
  obtain ⟨hfc, hfr⟩ := GlobalTheory.ThK.DescB.Nondeg.lev_reg hKP hM hH' hiso c hb0 hbj i hi f hf

  have hHe : IsHecke F E (X.α / X.β) :=
    ⟨hT.chars.heckeα.1.div' hT.chars.heckeβ.1, fun x => by
      rw [MonoidHom.div_apply, hT.chars.heckeα.2 x, hT.chars.heckeβ.2 x, div_one]⟩
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (a + a') := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, hT.chars.resα x, hT.chars.resβ x]
    split_ifs
    · simp
    · rcases neg_one_pow_eq_or ℂ a with e | e <;> simp [pow_add, e, div_neg]
  have hrk : a + a' = (d₁ - 2 * i) + 2 * (i + 1) := by
    have h1 := hH'.rank
    have h2 := (hiso i hi).1
    omega
  have hres₁ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (d₁ - 2 * i) := fun x => by
    rw [hres x, hrk, pow_add, pow_mul]
    simp
  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨hB, hT.geo.hV', hT.geo.hW, hT.geo.hM', hT.chars.heckeα, hHe, hT.chars.resα, hres, hT.weil'⟩

  obtain ⟨Z, r₁, s₁, hZ⟩ := GlobalTheory.ThK.SkewChain.skew_chain F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ hV' d₁ H' i₀ i₁ sp pl
    G.p hH' hiso i hi
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.ModelEx.model_exists F E σ B hB a' _ G.V' (reJ (sp i) Z) _ _ _ _ hT.geo.hV' hZ
  obtain ⟨om₀, hom₀⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B hB a' _ G.V' (reJ (sp i) Z) _ _ _ _ hT.geo.hV' hZ M₀ hM₀
    X.α (X.α / X.β) hT.chars.heckeα hHe hT.chars.resα hres₁
  have hP₀ : IsPair B M₀ X.α (X.α / X.β) om₀ G.q (a' - G.q) r₁ s₁ :=
    ⟨hB, hT.geo.hV', hZ, hM₀, hT.chars.heckeα, hHe, hT.chars.resα, hres₁, hom₀⟩
  obtain ⟨M₁, om₂, -, -, hco₁, hP₂, -, -⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B a' _ G.V' (reJ (sp i) Z) M₀ _ _ om₀ _ _ _ _ hP₀ co hco
  subst hco₁
  have hP₁ : IsPair B M₁ X.α (X.α / X.β) om₁ G.q (a' - G.q) r₁ s₁ :=
    ⟨hB, hT.geo.hV', hZ, hP₂.good, hT.chars.heckeα, hHe, hT.chars.resα, hres₁, hom⟩
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨c₀, hc₀, hc₀s⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hB.cm
  have hdet := GlobalTheory.ThK.DescB.Nondeg.det_ne_zero_of_cartan B (sp i) (hiso i hi).2.2.2.2.2.2.1
  have hJ : IsHermND σ (c₀ • (sp i).J.map σ) :=
    GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hP₁.skew.skew hdet hc₀ hc₀s
  have hφ : ∀ (g : UA σ (sp i).J) (g' : GAd σ (c₀ • (sp i).J.map σ)), g.1 = g'.1 →
      f ((toGAd hσ (sp i).J hc₀).symm g') = f g := fun g g' hg => congrArg f (Subtype.ext hg.symm)
  obtain ⟨K, hK, hA⟩ := GlobalTheory.T.matched_triple_witt_tower_descent hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH' hiso c hb0 hbj i hi f hf
    c₀ hc₀ hJ _ hφ
  have hC := GlobalTheory.T.theta_tower_descent_convergent hKP F E σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH' hiso c hb0 hbj i hi f hf hct
    c₀ hc₀ hJ _ hφ
  exact ⟨∅, fun v _ _ => GlobalTheory.ThK.LiftUnitV.unitary_pair hKP hP₁ hdet hfc hfr hdec ⟨c₀, K, _, hJ, hK, hA, hC, hφ⟩ hsm hμ h𝓕
    hΦ v⟩
