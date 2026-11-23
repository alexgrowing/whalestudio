import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativePreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnitHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevUniformBoundPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinatesStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay GlobalTheory.ThetaDenom
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaUnifSiegel

section Basic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem wordH_mem {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → ∀ Φ ∈ schA F κ, wordH ψ l Φ ∈ schA F κ := by
  intro l
  induction l with
  | nil => intro _ Φ hΦ; exact hΦ
  | cons w l ih =>
    intro hl Φ hΦ
    rw [wordH_cons]
    exact GlobalTheory.ThetaDecay.dH_mem_schA F κ ψ hψ w (hl w (by simp)) _ (ih (fun v hv => hl v (by simp [hv])) Φ hΦ)

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := by
  unfold ht
  exact heightGL_inv F g.1

theorem actAB_mul_inv {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (p : UA σ X.J × UA σ W.J)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : actAB (cA σ) p (actAB (cA σ) p⁻¹ u) = u := by
  simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (Matrix.transpose _), ← Matrix.transpose_mul]
  simp

theorem word_transport {n d : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) {C : ℝ}
    (hC : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w)
    (p : UA σ X.J × UA σ W.J) :
    ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), (∀ w ∈ l, IsArchUnit w) →
      ∃ (c : ℝ) (l' : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))), 0 ≤ c ∧
        c ≤ (C * ((ht p.1 : ℝ) * ht p.2)) ^ l.length ∧ (∀ w ∈ l', IsArchUnit w) ∧ l'.length = l.length ∧
        wordH B.ψ l (om p Φ) = (c : ℂ) • om p (wordH B.ψ l' Φ) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, [], zero_le_one, by simp, by simp, rfl, by simp⟩
  | cons w l ih =>
    intro hl
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := ih (fun v hv => hl v (by simp [hv]))
    have hw : IsArchUnit w := hl w (by simp)
    obtain ⟨c', hc'0, hc'le, w', hw', he'⟩ := hC p⁻¹ (M.co.e.symm w) (by simpa using hw)
    have hF' : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) :=
      wordH_mem B.ψ hP.base.std l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hT := GlobalTheory.T.heisenberg_derivative_equivariance F E σ B n d X W M χX χW om r s r' s' hP _ hF' p (actAB (cA σ) p⁻¹ (M.co.e.symm w))
      (by rw [he']; exact isArch_smul hw'.1 _)
    rw [actAB_mul_inv, LinearEquiv.apply_symm_apply, he', dH_realAd_smul, map_smul] at hT
    refine ⟨c * c', w' :: l', mul_nonneg hc0 hc'0, ?_, ?_, by simp [hlen], ?_⟩
    · rw [List.length_cons, pow_succ]
      have : c' ≤ C * ((ht p.1 : ℝ) * ht p.2) := by simpa [ht_inv] using hc'le
      exact mul_le_mul hcle this hc'0 (hc0.trans hcle)
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hw'
      · exact hl' v hv
    · rw [wordH_cons, he, dH_smul, hT, wordH_cons, smul_smul, Complex.ofReal_mul]

theorem lintegral_sq_norm_le_of_smul {α : Type} {m : MeasurableSpace α} (μ : Measure α) (f g : α → ℂ) (c : ℝ) (hc0 : 0 ≤ c)
    (he : f = (c : ℂ) • g) (B₀ K : ℝ) (hg : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B₀) (hcK : c ^ 2 ≤ K) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (K * max B₀ 0) := by
  have hcc : ‖(c : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc0, ENNReal.ofReal_pow hc0]
  subst he
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by rw [hcc]; exact ENNReal.ofReal_ne_top), hcc]
  calc ENNReal.ofReal (c ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ
      ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (max B₀ 0) :=
        by gcongr; exact hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (c ^ 2 * max B₀ 0) := (ENNReal.ofReal_mul (sq_nonneg c)).symm
    _ ≤ ENNReal.ofReal (K * max B₀ 0) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcK (le_max_right _ _))

theorem decay_arith (Q H m C₃ C₄ C₂ B₀ : ℝ) (a ℓ : ℕ) (hm0 : 0 ≤ m) (hm : m ≤ C₄ * H) (hH : 1 ≤ H)
    (key : Q ≤ C₃ * m ^ a * (1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0)) :
    Q ≤ (max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0))) * H ^ (a + 2 * ℓ) := by
  have hB₀' : (0 : ℝ) ≤ max B₀ 0 := le_max_right _ _
  have hC₂' : (1 : ℝ) ≤ max C₂ 1 := le_max_right _ _
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hm' : m ≤ max C₄ 1 * H := hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH0)
  have hBw0 : 0 ≤ (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0 := mul_nonneg (pow_nonneg (by positivity) _) hB₀'
  have h1B : 1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0 ≤ (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0) * H ^ (2 * ℓ) := by
    have hH1 : 1 ≤ H ^ (2 * ℓ) := one_le_pow₀ hH
    rw [mul_pow]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ max C₂ 1 by linarith) (2 * ℓ)]
  calc Q ≤ C₃ * m ^ a * (1 + (max C₂ 1 * H) ^ (2 * ℓ) * max B₀ 0) := key
    _ ≤ max C₃ 0 * (max C₄ 1 * H) ^ a * ((1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0) * H ^ (2 * ℓ)) := by
        gcongr
        · exact le_max_left _ _
    _ = _ := by
        rw [mul_pow, pow_add]
        ring

theorem std_char_denom (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) : ∃ D : ℕ, 0 < D ∧
    ∀ ξ : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) ξ * t) = 1) →
      ∃ o : 𝓞 F, (D : F) * ξ = o := by
  obtain ⟨D, hD, h⟩ := GlobalTheory.exists_den_traceDual_ringOfIntegers (F := F)
  refine ⟨D, hD, fun ξ hξ => h ξ fun o => GlobalTheory.TraceIntStd.trace_int_of_isStd ψ hψ _ fun t ht0 ht1 => ?_⟩
  have e : algebraMap F (AF F) (ξ * o) * t = algebraMap F (AF F) ξ * (algebraMap F (AF F) o * t) := by
    rw [map_mul, mul_assoc]
  rw [e]
  refine hξ _ ?_ fun v => ?_
  · rw [show (algebraMap F (AF F) (o : F) * t).1 = (algebraMap F (AF F) (o : F)).1 * t.1 from rfl, ht0, mul_zero]
  · rw [map_mul, AlgHom.commutes, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ht1 v)
    refine Valued.toNormedField.norm_le_one_iff.2 ?_
    first
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact v.valuation_le_one o)
      | (rw [show algebraMap F (Fv F v) (o:F) = ((o : F) : v.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact v.valuation_le_one o)
      | (exact (HeightOneSpectrum.coe_mem_adicCompletionIntegers v o))

theorem fin_step' {κ : Type} [Fintype κ] [DecidableEq κ] (ψ : AddChar (AF F) ℂ)
    (K : ℕ) (Ψ : (κ → AF F) → ℂ) (hfix : ∀ y, IsMulInt F K y → schr ψ (0, y) Ψ = Ψ) (x : κ → AF F) (ξ : κ → F)
    (hx : ∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) (hξ : Ψ x ≠ 0) (i : κ) (t : AF F) (ht0 : t.1 = 0)
    (ht1 : ∀ v, ‖evFin F v t‖ ≤ 1) : ψ (algebraMap F (AF F) ((K : F) * ξ i) * t) = 1 := by
  have e1 := congrFun (hfix _ (isMulInt_single K i t ht0 ht1)) x
  simp only [schr, dotProduct_single, zero_dotProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero] at e1
  have e2 := (mul_eq_right₀ hξ).1 e1
  rw [← e2]
  congr 1
  have e3 : algebraMap F (AF F) (ξ i) * t = x i * t := by
    refine Prod.ext ?_ ?_
    · show (algebraMap F (AF F) (ξ i)).1 * t.1 = (x i).1 * t.1
      rw [ht0, mul_zero, mul_zero]
    · show (algebraMap F (AF F) (ξ i)).2 * t.2 = (x i).2 * t.2
      rw [hx]
  rw [(algebraMap F (AF F)).map_mul, map_natCast, mul_assoc, e3]
  ring

variable {n d : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
  {om : Rep σ X W} {r s r' s' : ℕ}

theorem fix_moved (hP : IsPair B M χX χW om r s r' s') {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (g : UA σ X.J) (h : UA σ W.J) (z : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hz : M.co.rho B.ψ (((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * M.co.e.symm z *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ) Φ = Φ) :
    schr B.ψ z (om (g, h) Φ) = om (g, h) Φ := by
  set w' := M.co.e.symm z with hw'
  set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
    (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
  have hact : actAB (cA σ) (g, h) w = w' := by
    simp only [actAB, hw]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
      Matrix.mul_one]
  have himpl := hP.weil.isUSplitting.impl (g, h) w Φ hΦ
  rw [hz, hact] at himpl
  rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
  exact himpl.symm

theorem level_lin (hP : IsPair B M χX χW om r s r' s') {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∃ C : ℝ, ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ∧
      ∀ x a : Fin n × Fin d → AF F, (∀ i, evI F (a i) = 0 ∧ ∀ v, evFin F v (a i) ∈ v.adicCompletionIntegers F) →
        om (g, h) Φ (x + (m : AF F) • a) = om (g, h) Φ x := by
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom (M.co.e.trans (LinearEquiv.prodComm (AF F) _ _))
  refine ⟨m₀ * C, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · have : ((m₀ * N : ℕ) : ℝ) = m₀ * N := by push_cast; ring
    rw [this, mul_assoc (m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (y, 0) (om (g, h) Φ) = om (g, h) Φ := by
    intro y hy
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    exact fix_moved hP hΦ g h _ (hinv _ _ h2 h1)
  intro x a ha
  have hy : IsMulInt F (m₀ * N) (((m₀ * N : ℕ) : AF F) • a) := by
    refine ⟨fun i => ?_, fun v i => ?_⟩
    · change fstA F (((m₀ * N : ℕ) : AF F) * a i) = 0
      rw [map_mul]
      have h0 : fstA F (a i) = 0 := by
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (ha i).1
      rw [h0, mul_zero]
    · change ‖evFin F v (((m₀ * N : ℕ) : AF F) * a i)‖ ≤ _
      rw [map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (Valued.toNormedField.norm_le_one_iff.2 ((ha i).2 v))
  have := congrFun (hfix _ hy) x
  simpa [schr] using this

theorem denom_lin (hP : IsPair B M χX χW om r s r' s') {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : ∃ C : ℝ, ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨m₀, hm₀, hinv⟩ := GlobalTheory.ThetaLevel.heis_fix B.ψ hstd.1 Φ hΦ
  obtain ⟨D, hD, hcond⟩ := std_char_denom B.ψ hstd
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaLevel.transport_denom M.co.e
  refine ⟨D * m₀ * C, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨D * m₀ * N, Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · have : ((D * m₀ * N : ℕ) : ℝ) = D * m₀ * N := by push_cast; ring
    rw [this, mul_assoc (D * m₀ : ℝ) C]
    exact mul_le_mul_of_nonneg_left hNle (by positivity)
  intro x ξ hx hξ i
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y → schr B.ψ (0, y) (om (g, h) Φ) = om (g, h) Φ := by
    intro y hy
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    exact fix_moved hP hΦ g h _ (hinv _ _ h1 h2)
  obtain ⟨o, ho⟩ := hcond _ (fin_step' B.ψ (m₀ * N) _ hfix x ξ hx hξ i)
  have e : ((D * m₀ * N : ℕ) : F) * ξ i = o := by rw [← ho]; push_cast; ring
  rw [e]
  exact o.isIntegral_coe

theorem decay_unif (hP : IsPair B M χX χW om r s r' s') (N : ℕ) : ∃ k : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ,
    ∀ g h (x : Fin n × Fin d → AF F), ‖om (g, h) Φ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hstd : IsStd B.ψ := hP.base.std
  have hU := hP.weil.isUSplitting
  obtain ⟨μ, hμ, ℓ, a, C₃, h3⟩ := GlobalTheory.T.sobolev_uniform_bound_periodic F (Fin n × Fin d) N B.ψ hstd
  obtain ⟨C₂, h2⟩ := GlobalTheory.T.archimedean_unit_height_bound F E σ B n d X W M χX χW om r s r' s' hP
  refine ⟨a + 2 * ℓ, fun Φ hΦ => ?_⟩
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.ThetaSobolevBase.exists_l2_bound_heisenberg_word F (Fin n × Fin d) B.ψ hstd μ hμ Φ hΦ ℓ
  obtain ⟨C₄, h4⟩ := level_lin hP hΦ
  have hC₂ : ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) →
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ max C₂ 1 * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧
        M.co.e (actAB (cA σ) p u) = realAd F c • w := fun p u hu => by
    obtain ⟨c, h0, hle, w, hw, he⟩ := h2 p u hu
    exact ⟨c, h0, hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))), w, hw, he⟩
  refine ⟨max C₃ 0 * (max C₄ 1 ^ a * (1 + max C₂ 1 ^ (2 * ℓ) * max B₀ 0)), fun g h x => ?_⟩
  have hH : (1 : ℝ) ≤ (ht g : ℝ) * ht h :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1) (by exact_mod_cast one_le_heightGL F h.1)
  have hCH : (1 : ℝ) ≤ max C₂ 1 * ((ht g : ℝ) * ht h) := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hH
  have hΨ : om (g, h) Φ ∈ schA F (Fin n × Fin d) := hU.pres (g, h) Φ hΦ
  obtain ⟨m, hm1, hmle, hper⟩ := h4 g h
  have hwords : ∀ l : List ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)), l.length ≤ ℓ →
      (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH B.ψ l (om (g, h) Φ) x‖ₑ ^ 2 ∂μ ≤
        ENNReal.ofReal ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) * max B₀ 0) := by
    intro l hl hu
    obtain ⟨c, l', hc0, hcle, hl', hlen, he⟩ := word_transport hP hΦ hC₂ (g, h) l hu
    have hF : wordH B.ψ l' Φ ∈ schA F (Fin n × Fin d) := wordH_mem B.ψ hstd l' (fun v hv => (hl' v hv).1) Φ hΦ
    have hun := hU.unit μ hμ (g, h) _ hF
    have hc2 : c ^ 2 ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := by
      calc c ^ 2 ≤ ((max C₂ 1 * ((ht g : ℝ) * ht h)) ^ l.length) ^ 2 := pow_le_pow_left₀ hc0 hcle 2
        _ = (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * l.length) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (max C₂ 1 * ((ht g : ℝ) * ht h)) ^ (2 * ℓ) := pow_le_pow_right₀ hCH (by omega)
    exact lintegral_sq_norm_le_of_smul μ _ _ c hc0 he B₀ _ (hun.trans_le (hB₀ l' (by omega) hl')) hc2
  have key := h3 (om (g, h) Φ) hΨ m hm1 hper _ (mul_nonneg (pow_nonneg (by linarith) _) (le_max_right _ _)) hwords x
  exact decay_arith _ _ _ _ _ _ _ a ℓ (Nat.cast_nonneg m) hmle hH key

end Basic

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

open GlobalTheory.TorusTheta in

theorem theta_torus_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∃ k : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  obtain ⟨k₁, hdec₀⟩ := decay_unif hP₁ N₀
  refine ⟨k₁ + 1 * k₃, fun Φ hΦ => ?_⟩
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, hdec₁⟩ := hdec₀ (e Φ) heΦ
  have hdec : ∀ g h (x : Fin n × Fin d → AF F), ‖om₁ (g, h) (e Φ) x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N₀ ≤
      C₁ * ((ht g : ℝ) * ht h) ^ k₁ := fun g h x => by
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _))
      (add_le_add_right ?_ 1) N₀) (norm_nonneg _)) (hdec₁ g h x)
    exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i =>
      Finset.single_le_sum (f := fun i => ‖evI F (x i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  obtain ⟨C₂, hden⟩ := denom_lin hP₁ heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (1 * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (by rw [pow_one]; exact mul_le_mul_of_nonneg_right (le_abs_self _) hP0)) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + 1 * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (1 * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + 1 * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + 1 * k₃))) := by gcongr
    _ = _ := by ring

theorem transp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAd σ ((1 : E) • J.map σ)) :
    ∃ a' : UA σ J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • J.map σ) a := by
  have e := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ (c := (1 : E)) one_ne_zero
  refine ⟨⟨HA.mat (AF F) σ ((1 : E) • J.map σ) a, ?_⟩, rfl⟩
  have : HA.mat (AF F) σ ((1 : E) • J.map σ) a ∈ HR (AF F) σ ((1 : E) • J.map σ) := a.2
  rw [← e] at this
  exact this

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {C₀ K : Set (GAd σ J)} (hC₀ : IsCompact C₀) (hK : IsCompact K) :
    ∃ B : ℝ, ∀ x ∈ C₀, ∀ k ∈ K, (heightGL F (HA.mat (AF F) σ J (x * k)) : ℝ) ≤ B := by
  have hc : Continuous fun q : GAd σ J × GAd σ J => (heightGL F (HA.mat (AF F) σ J (q.1 * q.2)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_mul : Continuous fun p : GAd σ J × GAd σ J => p.1 * p.2)))
  obtain ⟨B, hB⟩ := ((hC₀.prod hK).image hc).bddAbove
  exact ⟨B, fun x hx k hk => hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩⟩

theorem theta_le_height_pow_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ (hσ : ∀ x, σ (σ x) = x) (e : E) (he : e ≠ 0) (Cf : Set (GFin σ (e • W.J.map σ))), IsCompact Cf →
      ∃ N : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), ∃ C : ℝ,
        ∀ (h : UA σ W.J) (g : UA σ X.J), projFin σ (e • W.J.map σ) (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J he h) ∈ Cf →
        ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ k ∈ K, g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om Φ g h‖ ≤ C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj hσ e he Cf _
  obtain ⟨Bd, hBd⟩ := ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  obtain ⟨k₁, hk₁⟩ := theta_torus_unif F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr c hc
  refine ⟨k₁, fun Φ hΦ => ?_⟩
  obtain ⟨C₁, h₁⟩ := hk₁ Φ hΦ
  refine ⟨|C₁| * (max Bd 0) ^ k₁, fun h g _ p hp t htc a ha k hk hg => ?_⟩
  obtain ⟨a', ha'⟩ := transp hσ X.J a
  have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
      HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
    have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
    rw [this]
    change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
    rw [ha', hg]
    rfl
  have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
    refine le_trans ?_ (le_max_left _ _)
    show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
    rw [hy]
    exact hBd _ (hconj p hp t htc a ha) k hk
  have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
  rw [mul_inv_cancel_left] at hb
  have hPq : 0 < ∏ i, t i ^ (Module.finrank ℚ F * d) := Finset.prod_pos fun i _ => pow_pos (htc.1 i) _
  have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
  have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hPq.le)
  calc C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
          (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
    _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring

end GlobalTheory.ThetaUnifSiegel

end
