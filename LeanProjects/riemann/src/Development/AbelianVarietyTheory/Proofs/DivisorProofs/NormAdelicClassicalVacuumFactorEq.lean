import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumThetaStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeanRealTorusNormalisedThetaMulConj
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaInnerProductEqRealTorusMean
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacFactor

section Mean

open scoped ENNReal Pointwise

theorem lintegral_translate {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {μ : Measure V} [μ.IsAddLeftInvariant] {L : AddSubgroup V} [Countable L] {F : Set V}
    (hF : IsAddFundamentalDomain L F μ) {φ : V → ℝ≥0∞} (hp : ∀ p ∈ L, ∀ s, φ (p + s) = φ s) (s : V) :
    ∫⁻ t in F, φ (s + t) ∂μ = ∫⁻ t in F, φ t ∂μ := by
  rw [← (hF.vadd_of_comm s).setLIntegral_eq hF φ fun p x => hp p p.2 x]
  exact (measurePreserving_add_left μ s).setLIntegral_comp_emb (measurableEmbedding_addLeft s) φ F

theorem integral_prod_eq {V U : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {μ : Measure V} [μ.IsAddLeftInvariant] [SigmaFinite μ]
    [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
    [SecondCountableTopology U] {ν : Measure U} [ν.IsAddLeftInvariant] [SigmaFinite ν] {n : ℕ}
    (e : V →+ (Fin n → U)) (he : Continuous e) (hs : Function.Surjective e)
    {A : AddSubgroup U} [Countable A] {F : Set U} (hF : IsAddFundamentalDomain A F ν)
    {Γ : AddSubgroup V} [Countable Γ] {F' : Set V} (hF' : IsAddFundamentalDomain Γ F' μ)
    (hΓ : ∀ γ ∈ Γ, ∀ k, e γ k ∈ A) {φ : U → ℝ} (hc : Continuous φ) (h0 : ∀ z, 0 ≤ φ z)
    (hp : ∀ p ∈ A, ∀ z, φ (p + z) = φ z) (hm : (∫ z in F, φ z ∂ν) / (ν F).toReal = 1) :
    ∫ v in F', ∏ k, φ (e v k) ∂μ = (μ F').toReal := by
  have hv : (ν F).toReal ≠ 0 := fun h => by simp [h] at hm
  obtain ⟨hv0, hv1⟩ := ENNReal.toReal_ne_zero.1 hv
  rw [div_eq_one_iff_eq hv] at hm
  have hi : IntegrableOn φ F ν := Integrable.of_integral_ne_zero (hm ▸ hv)
  have h1 : ∫⁻ z in F, ENNReal.ofReal (φ z) ∂ν = ν F := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0), hm, ENNReal.ofReal_toReal hv1]
  have hφ : Continuous fun z => ENNReal.ofReal (φ z) := ENNReal.continuous_ofReal.comp hc
  let G : (Fin n → U) → ℝ≥0∞ := fun z => ∏ k, ENNReal.ofReal (φ (z k))
  have hG : Measurable G := Finset.measurable_prod _ fun k _ => hφ.measurable.comp (measurable_pi_apply k)
  have hsw := lintegral_lintegral_swap (μ := μ.restrict F') (ν := Measure.pi fun _ : Fin n => ν.restrict F)
    (f := fun s t => G (e s + t)) (hG.comp ((he.comp continuous_fst).add continuous_snd).measurable).aemeasurable
  have e1 : ∀ s, ∫⁻ t, G (e s + t) ∂(Measure.pi fun _ : Fin n => ν.restrict F) = ν F ^ n := fun s => by
    have := GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod (μ := fun _ : Fin n => ν.restrict F)
      (f := fun k t => ENNReal.ofReal (φ (e s k + t)))
      fun k => (hφ.comp (continuous_const.add continuous_id)).measurable.aemeasurable
    refine this.trans ?_
    rw [Finset.prod_congr rfl fun k _ => (lintegral_translate hF (φ := fun z => ENNReal.ofReal (φ z))
      (fun p h z => by simp only [hp p h z]) (e s k)).trans h1]
    simp
  have e2 : ∀ t, ∫⁻ s in F', G (e s + t) ∂μ = ∫⁻ s in F', G (e s) ∂μ := fun t => by
    obtain ⟨t, rfl⟩ := hs t
    simp only [add_comm _ (e t), ← map_add]
    refine lintegral_translate hF' (φ := fun s => G (e s)) (fun p h z => ?_) t
    simp only [G, map_add, Pi.add_apply, hp _ (hΓ p h _)]
  simp only [e1, e2, lintegral_const, Measure.restrict_apply_univ, Measure.pi_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hsw
  rw [mul_comm] at hsw
  have e3 := (ENNReal.mul_left_inj (pow_ne_zero n hv0) (ENNReal.pow_ne_top hv1)).1 hsw
  have hcc : Continuous fun v => ∏ k, φ (e v k) :=
    continuous_finset_prod _ fun k _ => hc.comp ((continuous_apply k).comp he)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun v => Finset.prod_nonneg fun k _ => h0 _)
    hcc.aestronglyMeasurable, e3]
  simp only [G, ENNReal.ofReal_prod_of_nonneg fun k _ => h0 _]

end Mean

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}

theorem exists_meanOne {n : ℕ} (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1)
    {L : Lt E r} (hL : SelfD X L) {v : TF n g} (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : ∃ ϑ, IsTheta1 X bas idx w x L ϑ ∧ MeanOne X bas idx x L ϑ := by
  obtain ⟨b, hb, hb'⟩ := VacNorm.exists_sympl_of_selfD hs hL
  obtain ⟨c₁, c₂, C, hC, h₁, h₂, hx'⟩ := VacForm.thA_vacuum E r X g bas idx n hs hn w hw hw' L hL v hv b hb hb'
  obtain ⟨hh, hτ, hH, he, -⟩ := hx' x hx _ _ rfl rfl
  clear hx'
  obtain ⟨a₁, rfl⟩ : ∃ a₁ : Fin g → ℝ, c₁ = fun i => (a₁ i : ℂ) :=
    ⟨fun i => (c₁ i).re, funext fun i => by rcases h₁ i with h | h <;> simp [h]⟩
  obtain ⟨a₂, rfl⟩ : ∃ a₂ : Fin g → ℝ, c₂ = fun i => (a₂ i : ℂ) :=
    ⟨fun i => (c₂ i).re, funext fun i => by rcases h₂ i with h | h <;> simp [h]⟩
  set P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i with hP
  set Q : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i with hQ
  have hPu : IsUnit P.det := by
    by_contra hne
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp at hne
    · haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
      rw [nonsing_inv_apply_not_isUnit _ hne, det_zero] at hh
      exact not_isUnit_zero hh
  generalize hh' : P⁻¹ = h at *
  generalize hτ' : h * Q = τ at *
  have hhP : h * P = 1 := by rw [← hh', nonsing_inv_mul _ hPu]
  have hpv : ∀ m : Fin g ⊕ Fin g → ℤ, h *ᵥ pv X idx x (∑ j, m j • b j) =
      (fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
    intro m
    have : pv X idx x (∑ j, m j • b j) =
        P *ᵥ (fun i => (m (Sum.inl i) : ℂ)) + Q *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
      funext i
      rw [pv, per_sum]
      simp only [per_zsmul, Fintype.sum_sum_type, hP, hQ, pv]
      simp [mulVec, dotProduct, mul_comm]
    rw [this, mulVec_add, mulVec_mulVec, mulVec_mulVec, hhP, hτ', one_mulVec]
  have h0 : IsTheta1 X bas idx w x L fun z => CanTh.canTh τ a₁ a₂ (h *ᵥ z) := by
    refine ⟨(CanTh.differentiable_canTh hτ.2 a₁ a₂).comp (differentiable_pi.2 fun i => ?_), fun u hu => ?_⟩
    · simp only [dotProduct, mulVec]
      fun_prop
    · obtain ⟨m, rfl⟩ := (hb u).1 hu
      funext z
      have e := VacProd.thetaSign_mul_canonicalTheta_multiplier hL hw hw' (fun m => (hb _).2 ⟨m, rfl⟩) hb' h₁ he m
      simp only [Pi.smul_apply, smul_eq_mul, fock, hH]
      rw [mulVec_add h z (pv X idx x _), CanTh.canTh_add_period hτ.1 hτ.2 a₁ a₂ _ _ (hpv m)]
      generalize pv X idx x (∑ j, m j • b j) = p
      have e2 : cexp (-(((1 : ℕ) : ℂ) * Real.pi * ((h *ᵥ (z + (1 / 2 : ℂ) • p)) ⬝ᵥ
          ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ p)))) *
          cexp (Real.pi * Geo.Tor.hermForm (CanTh.imInv τ) (h *ᵥ z) (h *ᵥ p) +
            Real.pi / 2 * Geo.Tor.hermForm (CanTh.imInv τ) (h *ᵥ p) (h *ᵥ p)) = 1 := by
        rw [← Complex.exp_add, Complex.exp_eq_one_iff]
        refine ⟨0, ?_⟩
        simp only [Geo.Tor.hermForm, CanTh.imInv, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
        push_cast
        ring
      linear_combination (CanTh.canTh τ a₁ a₂ (h *ᵥ z)) * e + (CanTh.canTh τ a₁ a₂ (h *ᵥ z)) *
        (eps1 X w (∑ j, m j • b j) * CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i))) * e2
  let p : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) fun u v => by
    unfold pv; rw [per_add]; rfl
  let A : AddSubgroup (Fin g → ℂ) := L.toAddSubgroup.map p
  have hA : ∀ z, z ∈ A ↔ ∃ v ∈ L, z = pv X idx x v := fun z =>
    ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩
  have hA' : ∀ lam, lam ∈ A ↔ ∃ m n : Fin g → ℤ,
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    rw [hA]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, rfl⟩ := (hb u).1 hu
      exact ⟨_, _, hpv m⟩
    · rintro ⟨m, m', e⟩
      refine ⟨_, (hb _).2 ⟨Sum.elim m m', rfl⟩, ?_⟩
      have e' : h *ᵥ lam = h *ᵥ pv X idx x (∑ j, Sum.elim m m' j • b j) := e.trans (hpv (Sum.elim m m')).symm
      have := congrArg (h⁻¹ *ᵥ ·) e'
      simpa only [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec] using this
  obtain ⟨Fd, hFd, hm⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar
    g τ h _ _ A hτ.1 hτ.2 hh h₁ h₂ hA'
  have hpos : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hτ.2.det_pos)
  generalize Real.sqrt (2 ^ g * (τ.map Complex.im).det) = t at hm hpos
  refine ⟨fun z => (Real.sqrt t : ℂ) * CanTh.canTh τ a₁ a₂ (h *ᵥ z), ⟨h0.1.const_mul _, fun u hu => ?_⟩,
    A, Fd, hA, hFd, ?_⟩
  · funext z
    have := congrFun (h0.2 u hu) z
    simp only [Pi.smul_apply, smul_eq_mul, fock] at this ⊢
    linear_combination (Real.sqrt t : ℂ) * this
  · rw [← mul_inv_cancel₀ hpos.ne', ← hm, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    simp only [CanTh.canTh, CanTh.imInv]
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hpos.le, _root_.mul_assoc,
      mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
    congr 3
    have : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hH, this, re_ofReal_mul, VacNorm.re_dot, VacNorm.re_dot_star]
    push_cast; ring

theorem norm_sq_periodic {w : E} {L : Lt E r} {x : Frame X.Ψ r} {c : Fin g → ℝ}
    (hH : ∀ z z' : Fin g → ℂ, hx X bas idx x z z' = ∑ j, (c j : ℂ) * z j * conj (z' j))
    {ϑ : (Fin g → ℂ) → ℂ} (hϑ : IsTheta1 X bas idx w x L ϑ) {u : Fin r → E} (hu : u ∈ L) (z : Fin g → ℂ) :
    ‖ϑ (pv X idx x u + z)‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x (pv X idx x u + z) (pv X idx x u + z)).re) =
      ‖ϑ z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re) := by
  have hp := congrFun (hϑ.2 u hu) z
  have hε : ‖eps1 X w u‖ = 1 := by
    rw [eps1, Complex.norm_exp]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, fock] at hp
  generalize pv X idx x u = p at hp ⊢
  rw [← hp, add_comm p z, norm_mul, norm_mul, hε, _root_.one_mul, mul_pow, Complex.norm_exp,
      ← Real.exp_nat_mul, mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Nat.cast_one, _root_.one_mul, neg_re, re_ofReal_mul, hH, re_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

end GlobalTheory.AdTh.VacFactor

open GlobalTheory.AdTh.VacFactor in

theorem GlobalTheory.AdTh.norm_factor_eq_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → X.Λ = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∀ κ : ℂ, Reads θ V W hr X bas idx f (κ • v) x → (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) := by
  intro D ψ θ V W r g hr X bas idx hstd hinf hV he hm hs H _ ΛV ΛW _ _ _ _ x s hx f hf v hv κ hR
  subst hr
  have hw := GlobalTheory.Dict.VSetup.hostHalfRoot_add_conj_eq_one H
  have hi : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hL : SelfD X X.Λ := GlobalTheory.SW.Lev.selfD_of_sympl hs
  obtain ⟨hd, hu, hH⟩ := GlobalTheory.AdTh.hx_of_isONFr _ _ g _ X bas idx hs he x hx
  obtain ⟨ρ, hρ, hn⟩ := VacNorm.norm_factor_eq _ _ X g bas idx _ hs he _ hi hw _ hL v hv
  obtain ⟨ϑ, hϑ, hmean⟩ := exists_meanOne (idx := idx) hs he hi hw hL hv hd
  obtain ⟨κ₀, hκ₀⟩ := VacProd.prod_eq_mul_thA _ _ X g bas idx _ hs he _ hi hw _ hL v hv x hd ϑ hϑ
  have h₀ := hn x hd hu ϑ κ₀ hϑ hmean hκ₀
  suffices h : ρ = ‖κ‖ from fun x' hx' hu' ϑ' κ' h1 h2 h3 => (hn x' hx' hu' ϑ' κ' h1 h2 h3).trans h
  obtain ⟨X', m, hq', hq, bas', idx', hs', hΛ, -, -, -, -, -, hB⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hinf he hV hm hs
  obtain ⟨⟨B, hB1⟩, hB2⟩ := hB x hx
  let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs', he⟩
  obtain ⟨hCB, -, -, hz, hpv, -⟩ := hB2 B hB1
  have hd' : C.xB B ∈ X'.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hCB)
  obtain ⟨⟨e, hE⟩, -⟩ := GlobalTheory.Ker.zR_laws _ _ X' g X.p0 hq' bas' idx' V.rank hs' he _ hd'
  obtain ⟨⟨⟨μ, 𝓕⟩, hμ⟩, hone⟩ := hf.2.norm
  have hone := hone _ hμ
  obtain ⟨N, hN, hip⟩ := GlobalTheory.Ker.TorusMean.ipO_eq_mean D V W C μ 𝓕 hμ f f hf.2.theta hf.2.theta
  obtain ⟨⟨F', hF'⟩, hip⟩ := hip N hN dvd_rfl
  obtain ⟨A, F, hA, hF, hmean⟩ := hmean
  let φ : (Fin g → ℂ) → ℝ := fun z => ‖ϑ z‖ ^ 2 * Real.exp (-Real.pi * (Dict.hx X bas idx x z z).re)
  have hc : Continuous φ := by
    have := hϑ.1.continuous
    simp only [φ, hH]
    fun_prop
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable A := by
    refine ((Set.countable_range (pv X idx x)).mono fun z hz => ?_).to_subtype
    obtain ⟨u, -, rfl⟩ := (hA z).1 hz
    exact ⟨u, rfl⟩
  haveI := GlobalTheory.Ker.TorusMean.haar_WR X' (n := V.rank)
  have key := integral_prod_eq (μ := volume) (ν := volume) (e : GlobalTheory.Ker.WR X' V.rank →+ (Fin V.rank → Fin g → ℂ))
    e.continuous e.surjective hF hF' (fun γ hγ k => ?_) hc (fun z => by positivity) (fun p hp z => ?_) hmean
  · have h1 := hip F' hF' (fun v => ((‖κ‖ ^ 2 / ρ ^ 2 * ∏ k, φ (e v k) : ℝ) : ℂ)) fun w hw => ?_
    · have h2 : GlobalTheory.Ker.ipO μ 𝓕 f f = 1 := by
        simp only [GlobalTheory.Ker.ipO, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [integral_complex_ofReal]
        exact congrArg Complex.ofReal hone
      change ∫ v in F', ∏ k, φ (e v k) = _ at key
      rw [h2, integral_complex_ofReal, integral_const_mul, key] at h1
      have h3 : (1 : ℝ) = (volume F').toReal⁻¹ * (‖κ‖ ^ 2 / ρ ^ 2 * (volume F').toReal) := by exact_mod_cast h1
      have h4 : (volume F').toReal ≠ 0 := fun h => by simp [h] at h3
      rw [mul_left_comm, inv_mul_cancel₀ h4, mul_one, eq_comm, div_eq_one_iff_eq (by positivity)] at h3
      exact ((sq_eq_sq₀ (norm_nonneg _) hρ.le).1 h3).symm
    · have h2 : e (C.realPt w) = zOf θ V W rfl X idx x w := (hE _).trans (hz w)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hR.2 w hw]
      simp only [h2]
      generalize zOf θ V W rfl X idx x w = z
      congr 1
      simp only [φ, Finset.prod_mul_distrib, Finset.prod_pow, ← norm_prod, hκ₀, ← Real.exp_sum]
      rw [UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, norm_mul, h₀, Complex.norm_exp, mul_pow,
        ← Real.exp_nat_mul, show (-(Real.pi / 2 : ℂ)) = ((-(Real.pi / 2) : ℝ) : ℂ) by push_cast; ring,
        re_ofReal_mul, re_sum, ← Finset.mul_sum,
        show ∀ t : ℝ, ((2 : ℕ) : ℝ) * (-(Real.pi / 2) * t) = -Real.pi * t from fun t => by push_cast; ring]
      field_simp
  · obtain ⟨y, hy, rfl⟩ := (GlobalTheory.Ker.TorusMean.mem_latR_iff X' N γ).1 hγ
    rw [map_nsmul]
    refine nsmul_mem ((hA _).2 ⟨y k, hΛ ▸ hy k, ?_⟩) N
    exact (congrFun (hE _) k).trans (hpv (y k))
  · obtain ⟨u, hu, rfl⟩ := (hA p).1 hp
    exact norm_sq_periodic hH hϑ hu z
