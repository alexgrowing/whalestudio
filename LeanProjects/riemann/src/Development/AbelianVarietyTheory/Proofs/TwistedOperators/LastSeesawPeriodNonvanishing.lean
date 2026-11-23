import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibilityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LastSeesaw

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

private lemma eq_one_of_subOne_mulVec_ratV_eq_zero {S : HSp D} (g : GA D S)
    (h : ∀ x : Fin S.rank → D.host.E, (subOne S g).mulVec (ratV x) = 0) : g = 1 := by
  have hm : subOne S g = 0 := by
    ext i j
    have hr : (ratV (Pi.single j (1 : D.host.E)) : Fin S.rank → AE D) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk; simp [ratV]
      · simp [ratV, hk]
    have hj := congrFun (h (Pi.single j 1)) i
    rw [hr, Matrix.mulVec_single] at hj
    simpa using hj
  have h1 : ((matHom S g).1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) = 1 := sub_eq_zero.mp hm
  have h2 : matHom S g = matHom S 1 := by
    rw [map_one]
    exact Units.ext h1
  exact (HR (AF D.host.F) D.sp.cm.sig S.gram).subtype_injective h2

theorem eq_one_of_mem_flagN {S S₀ : HSp D} (d : HypDec S S₀ 0) {n : GA D S} (hn : n ∈ flagN d) : n = 1 := by
  have hle : flagN d ≤ ⊥ := by
    unfold flagN NFlag
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, hg⟩
    refine Subgroup.mem_bot.2 (eq_one_of_subOne_mulVec_ratV_eq_zero g fun x => ?_)
    obtain ⟨a, ha⟩ := hg x (Subsingleton.elim _ _)
    rw [ha]
    ext i
    simp [Matrix.mulVec, dotProduct]
  exact Subgroup.mem_bot.1 (hle hn)

theorem per_zero (J : JacL D 0) {L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (omz : Om J.W₀ L') (φ : GA D J.W₀ → ℂ)
    (f : GA D J.W → ℂ) (Φ₀ : WO J.W₀ L' → ℂ) :
    J.per ψ ζ' omz φ f Φ₀ = ∫ g in J.v0.𝓕, φ g * f (J.d.emb0 g) * star (omz (g, 1) Φ₀ 0) ∂J.v0.μ := by
  have hν : J.vN.ν J.vN.𝓝 = 1 := J.vN.unit.2.2
  have hX : ∀ (T : HSp D) (x : Mx D T.rank 0), J.d.extX T x = 0 := by
    intro T x
    rw [HypDec.extX_apply]
    ext i j
    simp [Matrix.mul_apply]
  have hs : symplO J.W L' (0 : WO J.W L') 0 = 0 := by
    have h := GlobalTheory.Asc.symplO_swap (S := J.W) (T := L') (0 : WO J.W L') 0
    have h2 : symplO J.W L' 0 0 + symplO J.W L' 0 0 = 0 := by
      nth_rw 1 [h]
      exact neg_add_cancel _
    have h3 : algebraMap D.host.F (AF D.host.F) 2 * symplO J.W L' 0 0 = 0 := by
      rw [map_ofNat, two_mul, h2]
    have h4 := congrArg (fun t => algebraMap D.host.F (AF D.host.F) 2⁻¹ * t) h3
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one, one_mul, mul_zero] at h4
    exact h4
  have hp : psiFlag ψ J.d 1 = 1 := by
    simp [psiFlag, upSum, psiE_zero]
  have hc : ∀ (h : GA D J.W₀) (n : flagN J.d),
      fjSrcFun ψ J.d ζ' omz φ f Φ₀ h n = φ h * f (J.d.emb0 h) * star (omz (h, 1) Φ₀ 0) := by
    intro h n
    have hn : n.1 = 1 := eq_one_of_mem_flagN J.d n.2
    simp only [fjSrcFun, thetaJS, jacS, ptS, cenS, hn, hp, hX, one_mul, Matrix.zero_mul, heisO_zero, star_one, mul_one]
    simp [symplOH, hs]
  simp only [JacL.per, fjSrc]
  congr 1
  funext h
  simp_rw [hc h]
  rw [setIntegral_const]
  simp [Measure.real, hν]

theorem integrable_norm_mul_pow {V : HSp D} (v : GlobalTheory.Unf.Vol V) {φ : GA D V → ℂ} (hφ : RapidDec V φ) (k : ℕ) :
    Integrable (fun g => ‖φ g‖ * quotHeight V g ^ k) (v.μ.restrict v.𝓕) := by
  have hm : AEStronglyMeasurable (fun g => ((quotHeight V g ^ k : ℝ) : ℂ)) (v.μ.restrict v.𝓕) :=
    (Complex.continuous_ofReal.comp ((GlobalTheory.Grow.continuous_quotHeight V).pow k)).aestronglyMeasurable
  have hI := hφ.integrableOn_mul_of_le v.haar v.fund hm (C := 1) (A := k) (fun g => by
    rw [one_mul, Complex.norm_real, norm_pow, Real.norm_of_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le])
  refine hI.norm.congr (ae_of_all _ fun g => ?_)
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, norm_pow, Real.norm_of_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le]
  ring

theorem tame_double {S X T L : HSp D} (o : OrthDec X T L) {χS χX : (AE D)ˣ →* Circle} {omX : Om S X}
    (hX : IsWeilDatumO ψ S X χS χX omX) (vS : GlobalTheory.Unf.Vol S) (vT : GlobalTheory.Unf.Vol T) {φ : GA D S → ℂ} {u : GA D T → ℂ}
    (hφ : RapidDec S φ) (hu : RapidDec T u) :
    (∀ f, IsThetaFunO ψ S X f → Integrable (fun y : GA D S × GA D T => φ y.1 * u y.2 * omX (y.1, o.emb (y.2, 1)) f 0)
      ((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕))) ∧
    Tame ψ S X fun f => ∫ y : GA D S × GA D T, φ y.1 * u y.2 * omX (y.1, o.emb (y.2, 1)) f 0
      ∂((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕)) := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D S).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D S).1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).1
  have := vS.haar
  have := vT.haar
  obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D X T L o
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have h1 := (hC 1).2
    have h2 := GlobalTheory.Grow.quotHeight_pos _ (o.emb ((1 : GA D T), 1))
    have h3 : 0 < quotHeight T (1 : GA D T) ^ a := pow_pos (GlobalTheory.Grow.quotHeight_pos _ _) a
    nlinarith
  have hemb : Continuous fun y : GA D S × GA D T => o.emb (y.2, 1) :=
    o.continuous_emb.comp (continuous_snd.prodMk continuous_const)
  have hint : ∀ k : ℕ, Integrable (fun y : GA D S × GA D T =>
      ‖φ y.1 * u y.2‖ * (quotHeight S y.1 * quotHeight X (o.emb (y.2, 1))) ^ k)
      ((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕)) := by
    intro k
    have h1 := integrable_norm_mul_pow vS hφ k
    have h2 := integrable_norm_mul_pow vT hu (a * k)
    have hp := (MeasureTheory.Integrable.mul_prod h1 h2).const_mul (C ^ k)
    refine hp.mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((((hφ.2.1.comp continuous_fst).mul (hu.2.1.comp continuous_snd)).norm).mul
        ((((GlobalTheory.Grow.continuous_quotHeight _).comp continuous_fst).mul ((GlobalTheory.Grow.continuous_quotHeight _).comp hemb)).pow k)).aestronglyMeasurable
    · have hS0 : 0 ≤ quotHeight S y.1 := (GlobalTheory.Grow.quotHeight_pos _ _).le
      have hX0 : 0 ≤ quotHeight X (o.emb (y.2, 1)) := (GlobalTheory.Grow.quotHeight_pos _ _).le
      have hle : quotHeight X (o.emb (y.2, 1)) ≤ C * quotHeight T y.2 ^ a := (hC y.2).2
      have hlin : quotHeight S y.1 * quotHeight X (o.emb (y.2, 1)) ≤ C * (quotHeight S y.1 * quotHeight T y.2 ^ a) := by
        nlinarith [mul_le_mul_of_nonneg_left hle hS0]
      have hpow : (quotHeight S y.1 * quotHeight X (o.emb (y.2, 1))) ^ k ≤
          C ^ k * (quotHeight S y.1 ^ k * quotHeight T y.2 ^ (a * k)) := by
        calc _ ≤ (C * (quotHeight S y.1 * quotHeight T y.2 ^ a)) ^ k := pow_le_pow_left₀ (mul_nonneg hS0 hX0) hlin k
          _ = _ := by rw [mul_pow, mul_pow, ← pow_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg hS0 hX0) k)), norm_mul]
      calc ‖φ y.1‖ * ‖u y.2‖ * (quotHeight S y.1 * quotHeight X (o.emb (y.2, 1))) ^ k
          ≤ ‖φ y.1‖ * ‖u y.2‖ * (C ^ k * (quotHeight S y.1 ^ k * quotHeight T y.2 ^ (a * k))) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = C ^ k * (‖φ y.1‖ * quotHeight S y.1 ^ k * (‖u y.2‖ * quotHeight T y.2 ^ (a * k))) := by ring
  exact GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ S X χS χX omX hX (GA D S × GA D T) ((vS.μ.restrict vS.𝓕).prod (vT.μ.restrict vT.𝓕))
    (fun y => φ y.1 * u y.2) (fun y => y.1) (fun y => o.emb (y.2, 1)) (fun _ => 0)
    ((hφ.2.1.comp continuous_fst).mul (hu.2.1.comp continuous_snd)).measurable continuous_fst hemb continuous_const hint

private lemma negSp_negSp (L : HSp D) : negSp (negSp L) = L := by
  cases L
  dsimp only [negSp]
  congr 1
  exact neg_neg _

private lemma exists_isWeilDatumO_star_of_isWeilDatumO_negSp {S L M : HSp D} (e : negSp (negSp L) = M) {χS χz : (AE D)ˣ →* Circle}
    {omz : Om S (negSp L)} (hz : IsWeilDatumO ψ S (negSp L) χS⁻¹ χz omz) :
    ∃ omL : Om S M, IsWeilDatumO ψ S M χS χz⁻¹ omL ∧
      ∀ g (f : WO S (negSp L) → ℂ) (F : WO S M → ℂ), HEq F (star f) → omL (g, 1) F 0 = star (omz (g, 1) f 0) := by
  subst e
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget omz, ?_, ?_⟩
  · simpa using (GlobalTheory.ConjWeil.conj_isWeilDatumO D ψ S (negSp L) χS⁻¹ χz omz hz).1
  · intro g f F hF
    obtain rfl := eq_of_heq hF
    have hcf : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f : WO S (negSp (negSp L)) → ℂ) = f := by
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [GlobalTheory.ConjWeil.conjTarget_apply, hcf]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem exists_conj {S L : HSp D} {χS χz : (AE D)ˣ →* Circle} {omz : Om S (negSp L)}
    (hz : IsWeilDatumO ψ S (negSp L) χS⁻¹ χz omz) : ∃ omL : Om S L, IsWeilDatumO ψ S L χS χz⁻¹ omL ∧
      ∀ g (f : WO S (negSp L) → ℂ), IsThetaFunO ψ S (negSp L) f →
        omL (g, 1) (star f : WO S L → ℂ) 0 = star (omz (g, 1) f 0) := by
  obtain ⟨omL, h1, h2⟩ := exists_isWeilDatumO_star_of_isWeilDatumO_negSp (negSp_negSp L) hz
  exact ⟨omL, h1, fun g f _ => h2 g f _ HEq.rfl⟩

theorem star_neg (hψ : IsStdChar D ψ (-1)) (S L : HSp D) (f : WO S (negSp L) → ℂ) :
    (IsThetaFunO ψ S (negSp L) f → IsThetaFunO ψ S L (star f : WO S L → ℂ)) ∧
      ∀ w : WO S L, heisO ψ S L w (star f : WO S L → ℂ) = (star (heisO ψ S (negSp L) w f) : WO S L → ℂ) := by
  have H := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S L
  have hcf : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (star f : WO S L → ℂ) = f := by
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  refine ⟨fun hf => (H.1 (star f)).1.1 (by rw [hcf]; exact hf), fun w => ?_⟩
  have h := (H.2 w (star f)).1
  rw [hcf] at h
  rw [h]
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem upLast : ∀ D : D7, UpLast D := by
  intro D ψ J X T L'' o Γ ΓL ΓX _ hLL ζ' χS χT χz om omX omz hom homX homz vT φ u hφ hu Ξ hΞ hne
  have hψ : IsStdChar D ψ (-1) := homX.std
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W₀).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W₀).1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D T).1
  have := J.v0.haar
  have := vT.haar
  obtain ⟨hIntg, hTame⟩ := tame_double (ψ := ψ) o homX J.v0 vT hφ hu

  have hval : ∀ F : WO J.W₀ X → ℂ, IsThetaFunO ψ J.W₀ X F →
      (∫ y : GA D J.W₀ × GA D T, φ y.1 * u y.2 * omX (y.1, o.emb (y.2, 1)) F 0
        ∂((J.v0.μ.restrict J.v0.𝓕).prod (vT.μ.restrict vT.𝓕))) =
      ∫ h in vT.𝓕, liftT omX J.v0.μ J.v0.𝓕 φ F (o.emb (h, 1)) * u h ∂vT.μ := by
    intro F hF
    rw [MeasureTheory.integral_prod_symm _ (hIntg F hF)]
    congr 1
    funext h
    rw [liftT_apply, ← integral_mul_const]
    congr 1
    funext g
    ring

  obtain ⟨f₁, f₂, hf₁, hf₂, hf₁0, hf₂0, hbox⟩ := hLL.ex
  have hf₀ : GlobalTheory.MixModel.OrthDec.boxT o J.W₀ (fun w => f₁ (J.d.ext0 T w)) (star f₂) ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hf₁0
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hf₂0
    have hx' : f₁ x ≠ 0 := hx
    have hy' : f₂ y ≠ 0 := hy
    intro h0
    have h1 := congrFun h0 ((o.resT J.W₀).symm ((GlobalTheory.WeilSrc.Zero.eqv J.d T).symm x, y))
    simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, Pi.star_apply] at h1
    rw [← GlobalTheory.WeilSrc.Zero.eqv_apply, AddEquiv.apply_symm_apply] at h1
    exact mul_ne_zero hx' (star_ne_zero.2 hy') h1

  obtain ⟨omL, homL, hconj⟩ := exists_conj (ψ := ψ) (S := J.W₀) (L := L'') homz
  have hpull := GlobalTheory.WeilSrc.Zero.isWeilDatumO_pull J.d hom
  have hTT := GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ X T L'' o J.W₀

  have hsee : ∀ (Φ : WO J.W T → ℂ) (Φ₀ : WO J.W₀ (negSp L'') → ℂ), IsThetaFunO ψ J.W T Φ →
      IsThetaFunO ψ J.W₀ (negSp L'') Φ₀ →
      (∫ y : GA D J.W₀ × GA D T, φ y.1 * u y.2 *
        omX (y.1, o.emb (y.2, 1)) (o.boxT J.W₀ (fun w => Φ (J.d.ext0 T w)) (star Φ₀)) 0
        ∂((J.v0.μ.restrict J.v0.𝓕).prod (vT.μ.restrict vT.𝓕))) =
      J.per ψ ζ' omz φ (liftS om vT.μ vT.𝓕 u Φ) Φ₀ := by
    intro Φ Φ₀ hΦ hΦ₀
    have hA : IsThetaFunO ψ J.W₀ T (fun w => Φ (J.d.ext0 T w)) := (GlobalTheory.WeilSrc.Zero.theta_iff J.d Φ).2 hΦ
    have hB : IsThetaFunO ψ J.W₀ L'' (star Φ₀ : WO J.W₀ L'' → ℂ) := (star_neg hψ J.W₀ L'' Φ₀).1 hΦ₀
    have hpt : ∀ (g : GA D J.W₀) (h : GA D T),
        omX (g, o.emb (h, 1)) (o.boxT J.W₀ (fun w => Φ (J.d.ext0 T w)) (star Φ₀)) 0 =
          om (J.d.emb0 g, h) Φ 0 * star (omz (g, 1) Φ₀ 0) := by
      intro g h
      rw [hTT.om_box χS χT χz⁻¹ omX _ omL homX hpull homL g h 1 _ _ hA hB, hTT.box_zero,
        hconj g Φ₀ hΦ₀, GlobalTheory.WeilSrc.Zero.pull_apply]
      have hfx : (fun x => Φ (J.d.ext0 T ((GlobalTheory.WeilSrc.Zero.eqv J.d T).symm x))) = Φ := by
        funext x
        rw [← GlobalTheory.WeilSrc.Zero.eqv_apply, AddEquiv.apply_symm_apply]
      simp only [hfx, map_zero]
    rw [per_zero, MeasureTheory.integral_prod _ (hIntg _ (hTT.box_theta _ _ hA hB))]
    congr 1
    funext g
    simp only [hpt, liftS_apply]
    rw [mul_comm (φ g) _, mul_assoc, ← integral_mul_const]
    congr 1
    funext h
    ring
  by_contra hcon
  push_neg at hcon
  apply hne
  rw [← hval Ξ hΞ.1]
  refine GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hψ J.W₀ X ΓX _ hTame _ hbox hf₀ (fun w hw => ?_) Ξ hΞ
  obtain ⟨hw1, hw2⟩ := hLL.ann w hw
  have hΦ := (GlobalTheory.Asc.annVac D ψ hψ J.W T Γ).1 f₁ hf₁ _ hw1
  have hΦ₀ := (GlobalTheory.Asc.annVac D ψ hψ J.W₀ (negSp L'') ΓL).1 f₂ hf₂ _ hw2
  have e1 : heisO ψ J.W₀ T (o.resT J.W₀ w).1 (fun w => f₁ (J.d.ext0 T w)) =
      fun w' => heisO ψ J.W T (J.d.ext0 T (o.resT J.W₀ w).1) f₁ (J.d.ext0 T w') := by
    have h := GlobalTheory.WeilSrc.Zero.heisO_eqv (ψ := ψ) J.d (o.resT J.W₀ w).1 f₁
    simp only [GlobalTheory.WeilSrc.Zero.eqv_apply] at h
    exact h.symm
  have e2 := (star_neg hψ J.W₀ L'' f₂).2 (o.resT J.W₀ w).2
  rw [o.heisO_boxT ψ J.W₀, e1, e2, hsee _ _ hΦ.1 hΦ₀.1]
  exact hcon _ _ hΦ hΦ₀

end GlobalTheory.LastSeesaw

end
