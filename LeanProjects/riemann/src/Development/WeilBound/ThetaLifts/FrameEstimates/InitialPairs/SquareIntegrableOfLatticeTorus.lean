import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.SquareIntegrableIntegralHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

noncomputable section

namespace PositivityTheory.ThKEst.Sq

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def TorBd (om : Rep σ X W) (fr : Frame σ X.J) (fr' : Frame σ W.J) (e : (Fin fr.r → ℝ) → (Fin fr'.r → ℝ) → ℝ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∀ (Ω : Set (UA σ X.J)) (Ω' : Set (UA σ W.J)), IsCompact Ω → IsCompact Ω' → ∃ A : ℝ≥0, ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r,
    ∀ κ ∈ Ω, ∀ κ' ∈ Ω', ‖theta om Φ (fr.a s * κ) (fr'.a t * κ')‖ₑ ≤ A * ENNReal.ofReal (Real.exp (e s t))

theorem pureA_mem' {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem torBd_sum {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hP : IsPair B M χX χW om r s r' s') {fr : Frame σ X.J} {fr' : Frame σ W.J}
    {e : (Fin fr.r → ℝ) → (Fin fr'.r → ℝ) → ℝ} {ι : Type} (T : Finset ι) (Φ : ι → (Fin n × Fin d → AF F) → ℂ)
    (hΦ : ∀ i, Φ i ∈ schA F (Fin n × Fin d)) (h : ∀ i, TorBd om fr fr' e (Φ i)) : TorBd om fr fr' e (∑ i ∈ T, Φ i) := by
  classical
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) :=
    (IsUWeilPair.isUSplitting hP.weil).pres
  induction T using Finset.induction_on with
  | empty => intro Ω Ω' _ _; exact ⟨0, fun s _ t _ κ _ κ' _ => by simp [theta, thetaSum]⟩
  | insert a T ha ih =>
    intro Ω Ω' h1 h2
    obtain ⟨A, hA⟩ := h a Ω Ω' h1 h2
    obtain ⟨A', hA'⟩ := ih Ω Ω' h1 h2
    refine ⟨A + A', fun s hs t ht κ hκ κ' hκ' => ?_⟩
    rw [Finset.sum_insert ha, theta, map_add,
      thetaSum_add F (hpres _ _ (hΦ a)) (hpres _ _ (Submodule.sum_mem _ fun i _ => hΦ i)), ENNReal.coe_add, add_mul]
    exact (enorm_add_le _ _).trans (add_le_add (hA s hs t ht κ hκ κ' hκ') (hA' s hs t ht κ hκ κ' hκ'))

theorem torBd_pure (hC : LatCpt) {B : Base F E} {M : Model σ X W} {om : Rep σ X W} (hB : B.IsGood σ) (hX : EpsHerm σ X.J)
    (hW : EpsHerm σ W.J) {fr : Frame σ X.J} {fr' : Frame σ W.J} {𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)}
    {S : Set (Matrix (Fin n) (Fin d) E)} (hS : SqBound B M om 𝓕 S) {e e₂ : (Fin fr.r → ℝ) → (Fin fr'.r → ℝ) → ℝ} {N : ℕ}
    (hT : ∀ C, IsCompact C → ∃ K : ℝ≥0, ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r,
      latSum B.emb C N S (fr.a s) (fr'.a t) ≤ K * ENNReal.ofReal (Real.exp (e₂ s t)))
    (he : ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r, e₂ s t ≤ 2 * e s t) (f : SInf F (Fin n × Fin d))
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ 𝓕) : TorBd om fr fr' e (pureA F f φ) := by
  intro Ω Ω' h1 h2
  obtain ⟨p, C, -, hCc, hb⟩ := hS φ hφ N
  obtain ⟨C', K, hC', hK⟩ := hC F E σ hB.cm B.emb n d X.J W.J hX hW Ω Ω' h1 h2 C N hCc
  obtain ⟨K', hK'⟩ := hT C' hC'
  refine ⟨(p f).toNNReal * NNReal.sqrt (K * K'), fun s hs t ht κ hκ κ' hκ' => ?_⟩
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ((hb f _ _).trans ?_)
  have e1 : ((NNReal.sqrt (K * K') : ℝ≥0) : ℝ≥0∞) ^ 2 = K * K' := by
    rw [← ENNReal.coe_pow, NNReal.sq_sqrt, ENNReal.coe_mul]
  have e2 : ENNReal.ofReal (Real.exp (e₂ s t)) ≤ ENNReal.ofReal (Real.exp (e s t)) ^ 2 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by exact_mod_cast he s hs t ht))
  calc _ ≤ ENNReal.ofReal (p f) ^ 2 * (K * (K' * ENNReal.ofReal (Real.exp (e s t)) ^ 2)) := by
        refine mul_le_mul_right ((hK S _ _ κ hκ κ' hκ').trans (mul_le_mul_right ((hK' s hs t ht).trans ?_) _)) _
        exact mul_le_mul_right e2 _
    _ = _ := by
        rw [ENNReal.coe_mul, mul_pow, mul_pow, e1]
        simp only [ENNReal.ofReal, mul_assoc]

theorem square_integrable_of_torus_bound (hG : GrpTop) (hTh : ThetaBasic) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (hX : EpsHerm σ X.J) (hW : EpsHerm σ W.J) {fr : Frame σ X.J}
    {fr' : Frame σ W.J} (hI : SiegelInt fr) (hI' : SiegelInt fr') {U : (Fin fr.r → ℝ) → ℝ} {V : (Fin fr'.r → ℝ) → ℝ}
    (hUm : Measurable U) (hVm : Measurable V)
    (hU : ∫⁻ s in Cone fr.r, ENNReal.ofReal (Real.exp (U s)) *
      ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n s))) < ⊤)
    (hV : ∫⁻ t in Cone fr'.r, ENNReal.ofReal (Real.exp (2 * V t)) *
      ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 d t))) < ⊤)
    {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (hb : TorBd om fr fr' (fun s t => U s + V t) Φ)
    (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ) :
    IntegrableOn (fun h => ‖M.I om Φ h‖ ^ 2) 𝓕 μ := by
  obtain ⟨lc, sc, -⟩ := hG F E σ hP.base.cm n X.J hX
  obtain ⟨lc', sc', -⟩ := hG F E σ hP.base.cm d W.J hW
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have := hP.good.haar
  have : SigmaCompactSpace (UA σ X.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) := @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  obtain ⟨hcont, hinv, -⟩ := (hTh F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ
  obtain ⟨K, Ω, hK, hΩ, H⟩ := hI M.μ M.dom hP.good.haar hP.good.dom
  obtain ⟨K', Ω', hK', hΩ', H'⟩ := hI' μ 𝓕 hμ h𝓕
  obtain ⟨A, hA⟩ := hb Ω Ω' hΩ hΩ'
  have hsm : StronglyMeasurable (M.I om Φ) :=
    StronglyMeasurable.integral_prod_left (μ := M.μ.restrict M.dom) (f := fun g h => theta om Φ g h)
      hcont.stronglyMeasurable
  set IU := ∫⁻ s in Cone fr.r, ENNReal.ofReal (Real.exp (U s)) *
      ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n s)))
  have h1 : ∀ t ∈ Cone fr'.r, ∀ κ' ∈ Ω', ‖M.I om Φ (fr'.a t * κ')‖ₑ ≤ (K * A * IU) * ENNReal.ofReal (Real.exp (V t)) := by
    intro t ht κ' hκ'
    have a1 := H (fun s => (A * ENNReal.ofReal (Real.exp (V t))) * ENNReal.ofReal (Real.exp (U s)))
      (measurable_const.mul (Real.measurable_exp.comp hUm).ennreal_ofReal)
      (fun g => ‖theta om Φ g (fr'.a t * κ')‖ₑ) (hcont.comp (continuous_id.prodMk continuous_const)).measurable.enorm
      (fun γ hγ g => by have := hinv γ hγ 1 (one_mem _) g (fr'.a t * κ'); rw [one_mul] at this; simp only [this])
      (fun s hs κ hκ => (hA s hs t ht κ hκ κ' hκ').trans (le_of_eq (by
        rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]; ring)))
    refine (enorm_integral_le_lintegral_enorm _).trans (a1.trans (le_of_eq ?_))
    simp only [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm IU]
  have hc : K * A * IU ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hK.ne ENNReal.coe_ne_top) hU.ne
  have h2 := H' (fun t => (K * A * IU) ^ 2 * ENNReal.ofReal (Real.exp (2 * V t)))
    (measurable_const.mul (Real.measurable_exp.comp (hVm.const_mul 2)).ennreal_ofReal)
    (fun h => ‖M.I om Φ h‖ₑ ^ 2) (hsm.measurable.enorm.pow_const 2)
    (fun γ hγ h => by
      have : M.I om Φ (γ * h) = M.I om Φ h := by
        unfold Model.I
        congr 1
        funext g
        have := hinv 1 (one_mem _) γ hγ g h
        rwa [one_mul] at this
      simp only [this])
    (fun t ht κ' hκ' => (pow_le_pow_left' (h1 t ht κ' hκ') 2).trans (le_of_eq (by
      rw [mul_pow _ (ENNReal.ofReal _), ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]; norm_num)))
  refine ⟨(hsm.norm.pow 2).aestronglyMeasurable, ?_⟩
  have e : ∀ h, ‖‖M.I om Φ h‖ ^ 2‖ₑ = ‖M.I om Φ h‖ₑ ^ 2 := fun h => by rw [enorm_pow, enorm_norm]
  unfold HasFiniteIntegral
  simp only [e]
  refine h2.trans_lt (ENNReal.mul_lt_top hK' ?_)
  simp only [mul_assoc ((K * A * IU) ^ 2)]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hc.lt_top) hV

theorem finrank_pos' (E : Type) [Field E] [NumberField E] : (0 : ℝ) < Module.finrank ℚ E := by
  exact_mod_cast Module.finrank_pos

theorem square_integrable_of_lattice_torus (hG : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hTh : ThetaBasic) (hq : SqAll) (hF : SoFin) (hC : LatCpt)
    (hT : LatTor) : SquareIntegrableWeilRange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP h1 h2 μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hX, -, hr⟩ := hE F E σ B hP.base n X r s (Or.inl hP.herm)
  obtain ⟨hW, -, hr'⟩ := hE F E σ B hP.base d W r' s' (Or.inr hP.skew)
  obtain ⟨fr, hf, -, -, hI, -⟩ := hS F E σ hP.base.cm n X.J hX
  obtain ⟨fr', hf', -, -, hI', -⟩ := hS F E σ hP.base.cm d W.J hW
  have hD := finrank_pos' E
  obtain ⟨a1, a2⟩ := square_integrable_integral_holds n d fr.r fr'.r _ hD (by have := hr fr hf; omega) (by have := hr' fr' hf'; omega)
  obtain ⟨N, hN⟩ := hT F E σ hP.base.cm B.emb n d X.J W.J hX hW fr fr' hf hf'
  obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hP).2.1 Φ hΦ
  refine square_integrable_of_torus_bound hG hTh hP hX hW hI hI' (U := fun s => Module.finrank ℚ E * (d / 2 * ∑ i, s i))
    (V := fun t => Module.finrank ℚ E * (n * ∑ j, t j) / 2) (by fun_prop) (by fun_prop) a1 ?_ hΦ ?_ μ 𝓕 hμ h𝓕
  · simpa only [mul_div_cancel₀ _ (two_ne_zero (α := ℝ))] using a2
  · refine torBd_sum hP _ _ (fun i => pureA_mem' _ (hφ i)) fun i =>
      torBd_pure hC hP.base hX hW (hq F E σ B n d X W M χX χW om r s r' s' hP) hN (fun s hs t ht => ?_) _ (hφ i)
    have := mul_le_mul_of_nonneg_left (posWt' n d _ _ s t hs ht).1 hD.le
    linarith

theorem exp_cancel {r : ℕ} (c : ℝ) (hc : 0 < c) (ρ : (Fin r → ℝ) → ℝ) :
    ∫⁻ t in Cone r, ENNReal.ofReal (Real.exp (ρ t - c * ∑ i, t i)) * ENNReal.ofReal (Real.exp (-ρ t)) < ⊤ := by
  refine lt_of_eq_of_lt (lintegral_congr fun t => ?_) (coneAff r (-c) 0 fun k _ _ => by simpa using hc)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [zero_mul, add_zero, ← Finset.mul_sum]
  ring

theorem square_integrable_orthogonal_case (hG : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hTh : ThetaBasic) (hq : SqSo) (hF : SoFin) (hC : LatCpt)
    (hT : LatFull) : SquareIntegrableSiegelSet := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP h1 ⟨Y, y1, y2, y3⟩ μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hX, -, hr⟩ := hE F E σ B hP.base n X r s (Or.inl hP.herm)
  obtain ⟨hW, -, hr'⟩ := hE F E σ B hP.base d W r' s' (Or.inr hP.skew)
  obtain ⟨fr, hf, -, -, hI, -⟩ := hS F E σ hP.base.cm n X.J hX
  obtain ⟨fr', hf', -, -, hI', -⟩ := hS F E σ hP.base.cm d W.J hW
  have hD := finrank_pos' E
  set D : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ)
  obtain ⟨m₀, hm₀⟩ := exponent_bound_orthogonal_case n d fr.r fr'.r Y ((hr fr hf).trans y1) ((hr' fr' hf').trans y2) y3 h1
  obtain ⟨N, hN⟩ := hT F E σ hP.base.cm B.emb n d X.J W.J hX hW fr fr' hf hf' ⌈2 * D * m₀⌉₊
  obtain ⟨b1, -, b3, -⟩ := hF F E σ B n d X W M χX χW om r s r' s' hP
  have hΦ' := b3 Φ hΦ
  obtain ⟨m, f, φ, hφ, rfl⟩ := b1 Φ hΦ
  refine square_integrable_of_torus_bound hG hTh hP hX hW hI hI' (U := fun s => D * rho2 n s - D / (4 * (fr.r + 1)) * ∑ i, s i)
    (V := fun t => (D * rho2 d t - D / 2 * ∑ j, t j) / 2) (by unfold rho2; fun_prop) (by unfold rho2; fun_prop)
    (exp_cancel _ (by positivity) _) ?_ hΦ' ?_ μ 𝓕 hμ h𝓕
  · simpa only [mul_div_cancel₀ _ (two_ne_zero (α := ℝ))] using exp_cancel (D / 2) (by positivity) fun t => D * rho2 d t
  · refine torBd_sum hP _ _ (fun i => pureA_mem' _ (hφ i).1) fun i =>
      torBd_pure hC hP.base hX hW (hq F E σ B n d X W M χX χW om r s r' s' hP) hN (fun s hs t ht => ?_) _ (hφ i)
    have a1 := mul_le_mul_of_nonneg_left (hm₀ s hs t ht) hD.le
    have a2 := mul_le_mul_of_nonneg_right (Nat.le_ceil (2 * D * m₀)) (posWt' n d _ _ s t hs ht).2.1
    have e : D * ((∑ i, s i) / (4 * ((fr.r : ℝ) + 1))) = D / (4 * (fr.r + 1)) * ∑ i, s i := by ring
    nlinarith

omit [NumberField E] in
theorem polData_le {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  have h3 := (h2.and hM.std).mono fun _ h => h.1.trans h.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem sqInt_of (hT : TriplePair) (h1 : SquareIntegrableWeilRange) (h2 : SquareIntegrableSiegelSet) : SqInt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr μ 𝓕 hμ h𝓕
  obtain ⟨p1, p2, p3⟩ := hT F E σ B a a' G X om om' hTr
  have g1 := hTr.geo.lt
  have g2 := hTr.geo.aBig
  exact ⟨fun Φ hΦ => h1 F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 (Or.inl p3) (Or.inr (by omega)) μ 𝓕 hμ h𝓕 Φ
      (polData_le hTr.geo.hM hΦ),
    fun Φ hΦ => h2 F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 (by omega) ⟨G.p + G.q, by omega, by omega, g2⟩ μ 𝓕 hμ h𝓕 Φ hΦ.2⟩

end PositivityTheory.ThKEst.Sq
