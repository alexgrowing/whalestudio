import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Transport
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.IfaceSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ProductBoundOfFactorBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportIntA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

namespace TransportInt

theorem cayley_signature {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) : pOf ε = k + r ∧ qOf ε = r + 1 :=
  TransportIntA.cayley_signature' hP

theorem frob_conj_ge {k r : ℕ} {P : Mat k r} (hP : IsUnit P.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Mat k r, c * Formalism.FourierDecayAlt.B.gN g ≤ frob (P * g * P⁻¹) := by
  letI : SeminormedAddCommGroup (Mat k r) := Matrix.frobeniusSeminormedAddCommGroup
  have hF : ∀ A : Mat k r, frob A = ‖A‖ := by
    intro A
    unfold frob
    rw [Matrix.frobenius_norm_def]
    simp only [Real.sqrt_eq_rpow, Real.rpow_two]
  have hG : ∀ A : Mat k r, Formalism.FourierDecayAlt.B.gN A = ‖A‖ := by
    intro A
    rw [← hF]
    unfold Formalism.FourierDecayAlt.B.gN frob
    simp only [Complex.normSq_eq_norm_sq]
  have hinv2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hK0 : 0 ≤ ‖P⁻¹‖ * ‖P‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hK1 : (0 : ℝ) < ‖P⁻¹‖ * ‖P‖ + 1 := by linarith
  refine ⟨1 / (‖P⁻¹‖ * ‖P‖ + 1), div_pos one_pos hK1, fun g => ?_⟩
  rw [hG, hF]
  have hg : P⁻¹ * (P * g * P⁻¹) * P = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv2, Matrix.one_mul, Matrix.mul_assoc, hinv2,
      Matrix.mul_one]
  have hle : ‖g‖ ≤ ‖P⁻¹‖ * ‖P‖ * ‖P * g * P⁻¹‖ := by
    calc ‖g‖ = ‖P⁻¹ * (P * g * P⁻¹) * P‖ := by rw [hg]
      _ ≤ ‖P⁻¹ * (P * g * P⁻¹)‖ * ‖P‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ := by
          gcongr
          exact Matrix.frobenius_norm_mul _ _
      _ = ‖P⁻¹‖ * ‖P‖ * ‖P * g * P⁻¹‖ := by ring
  have hX : 0 ≤ ‖P * g * P⁻¹‖ := norm_nonneg _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK1]
  nlinarith

theorem pi_isometry {k r : ℕ} {u : Fin k → ℝ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π) : ∀ h ∈ UWset k r z, ∀ ξ : Vp, ‖π h ξ‖ = ‖ξ‖ := by
  intro h hh ξ
  obtain ⟨g, hg, hρ⟩ := hπ
  obtain ⟨h₀, hh₀, rfl⟩ := TransportGeo.uw_eq_frame hT hg hh
  exact hρ.2.2.1.2.1 h₀ hh₀ ξ

theorem integrand_aesm {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {u : Fin k → ℝ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (T : S7.KType ε (lowK ε lam)) {μ : Fin (2 * r + k + 1) → ℤ} (hμ : S7.IsMu lam μ)
    {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)} {μW μN : Measure (Mt k r)}
    (hB : IsBData z c u π μW μN) (v₁ v₂ : T.V) (ξ : Vp) {x₀ x : Mat k r}
    (hx₀ : x₀ ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    AEStronglyMeasurable (fun p : Mt k r × Mt k r =>
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  obtain ⟨g, hg, hρ⟩ := hπ
  have hgd : IsUnit g.det := TransportGeo.uh_det hg.1
  let β : Mat k r → Matrix (Fin k) (Fin k) ℂ := fun h i j =>
    (g⁻¹ * h * g) ⟨r + i.val, by omega⟩ ⟨r + j.val, by omega⟩
  have hβc : Continuous β := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply _).comp ((continuous_apply _).comp
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const))
  have hblk : ∀ h₀ : Matrix (Fin k) (Fin k) ℂ, β (g * Formalism.MainNotions.S.blockW k r h₀ * g⁻¹) = h₀ := by
    intro h₀
    have e : g⁻¹ * (g * Formalism.MainNotions.S.blockW k r h₀ * g⁻¹) * g = Formalism.MainNotions.S.blockW k r h₀ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hgd, Matrix.nonsing_inv_mul _ hgd,
        Matrix.mul_one]
    funext i j
    simp only [β, e, Formalism.MainNotions.S.blockW]
    simp
  have hβπ : ∀ h ∈ UWset k r z, β h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) ∧
      π h = π (g * Formalism.MainNotions.S.blockW k r (β h) * g⁻¹) := by
    intro h hh
    obtain ⟨h₀, hh₀, rfl⟩ := TransportGeo.uw_eq_frame hT hg hh
    rw [hblk]
    exact ⟨hh₀, rfl⟩
  have hUWc := Transport.uw_closedSubgroup k r z
  have hNc := Transport.n_closedSubgroup k r
  set A : Set (Mt k r × Mt k r) := {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r} with hA
  have hfst : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)) := continuous_fst
  have hsnd : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) := continuous_snd
  have hAm : MeasurableSet A :=
    ((hUWc.closed.preimage hfst).inter (hNc.closed.preimage hsnd)).measurableSet
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by
    rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
    rw [ae_iff]; simpa using hN.2.2.1
  have hpae : ∀ᵐ p ∂(μW.prod μN), p ∈ A :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  rw [← Measure.restrict_eq_self_of_ae_mem hpae]
  refine ContinuousOn.aestronglyMeasurable ?_ hAm

  have h12 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r) * Matrix.of p.2) :=
    hfst.matrix_mul hsnd
  have hm : Continuous (fun p : Mt k r × Mt k r =>
      P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹) :=
    (continuous_const.matrix_mul (continuous_const.matrix_mul (h12.matrix_mul continuous_const))).matrix_mul
      continuous_const
  have hPs : ContinuousOn (fun p : Mt k r × Mt k r =>
      S7.PsiM T μ (P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹)) A := by
    refine (S7.psiM_continuousOn T μ hμ).comp hm.continuousOn fun p hp => ?_
    have hs : Matrix.of p.1 * Matrix.of p.2 * x ∈ UH (Hpk k r) :=
      Transport.uh_mul (Transport.uh_mul hp.1.1 hp.2.1) hx
    exact (Transport.uh_facts hP (Transport.uh_mul (Transport.uh_facts hP hx₀).2.1 hs)).2.2
  have hf1 : ContinuousOn (fun p : Mt k r × Mt k r =>
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x))) A := by
    unfold psiCoef
    exact continuousOn_const.inner (hPs.clm_apply continuousOn_const)

  have hψc : Continuous (Formalism.MainNotions.S.psiGen k r z c) := by
    unfold Formalism.MainNotions.S.psiGen
    refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_const.mul ?_))))
    by_cases hcond : a.val + 1 < r
    · simp only [Formalism.MainNotions.S.ellA, dif_pos hcond]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [Formalism.MainNotions.S.ellA, dif_neg hcond]
      exact (continuous_apply (Formalism.QuantumDeterminants.eI k r a)).comp
        (continuous_id.matrix_mulVec (continuous_const (y := z)))
  have hinvc : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r)⁻¹) A := by
    have hc : Continuous (fun p : Mt k r × Mt k r => Hpk k r * (Matrix.of p.1 : Mat k r)ᴴ * Hpk k r) :=
      (continuous_const.matrix_mul hfst.matrix_conjTranspose).matrix_mul continuous_const
    refine hc.continuousOn.congr fun p hp => ?_
    exact Matrix.inv_eq_left_inv (TransportGeo.uh_inv_eq hp.1.1)
  have hρc : ContinuousOn (fun h₀ => π (g * Formalism.MainNotions.S.blockW k r h₀ * g⁻¹) ξ)
      (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) := hρ.2.2.1.2.2 ξ
  have hf2' : ContinuousOn (fun p : Mt k r × Mt k r =>
      π (g * Formalism.MainNotions.S.blockW k r (β (Matrix.of p.1 : Mat k r)⁻¹) * g⁻¹) ξ) A :=
    hρc.comp (hβc.comp_continuousOn hinvc) fun p hp => (hβπ _ (hUWc.inv_mem _ hp.1)).1
  have hf2 : ContinuousOn (fun p : Mt k r × Mt k r =>
      chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) A := by
    have e : Set.EqOn (fun p : Mt k r × Mt k r =>
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ)
        (fun p => star (Formalism.MainNotions.S.psiGen k r z c (Matrix.of p.2)) •
          π (g * Formalism.MainNotions.S.blockW k r (β (Matrix.of p.1 : Mat k r)⁻¹) * g⁻¹) ξ) A := by
      intro p hp
      simp only [chiInv]
      rw [(hβπ _ (hUWc.inv_mem _ hp.1)).2]
    refine ContinuousOn.congr ?_ e
    exact ((continuous_star.comp (hψc.comp hsnd)).continuousOn).smul hf2'
  exact hf1.smul hf2

theorem integrable_coef_of (hIS : S0.IntSStatement) (hDD : DecDerivStatement)
    {k r : ℕ} (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} (hgap : GapLap ε lam h) {u : Fin k → ℝ}
    {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (T : S7.KType ε (lowK ε lam)) {μ : Fin (2 * r + k + 1) → ℤ} (hμ : S7.IsMu lam μ)
    {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Vp →L[ℂ] Vp)} {μW μN : Measure (Mt k r)}
    (hB : IsBData z c u π μW μN) (v₁ v₂ : T.V) (ξ : Vp) {x₀ x : Mat k r}
    (hx₀ : x₀ ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    Integrable (fun p : Mt k r × Mt k r =>
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) •
        chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN) := by
  obtain ⟨hz, hT, hc, hπ, hW, hN⟩ := hB
  obtain ⟨hp, hq⟩ := cayley_signature hP
  have hq0 : 1 ≤ S7.q0 ε := by
    unfold S7.q0
    rw [hp, hq]
    omega
  have hHC : S7.IsHCParam lam := by
    refine ⟨hgap.1, fun a => ⟨μ a + ((a : ℕ) : ℤ) - ((2 * r + k + 1 : ℕ) : ℤ) + 1, ?_⟩⟩
    have h1 := hμ a
    simp only [ReciprocityTheory.ChartRestriction.DS.rho] at h1
    push_cast at h1 ⊢
    linarith
  obtain ⟨C, hC⟩ := hDD _ ε lam h T μ hHC hgap.2.1 hgap.2.2 hq0 hμ [] v₁ v₂
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  obtain ⟨c0, hc0, hcg⟩ := frob_conj_ge hPd
  set a := h / (8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) with ha
  have hq0' : ((S7.q0 ε : ℕ) : ℝ) = (r : ℝ) + 1 := by
    unfold S7.q0
    rw [hp, hq, min_eq_right (by omega)]
    push_cast
    ring
  have hsp : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hb : S0.bS k r < a := by
    have h3 : 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) *
        (4 * max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (min (pOf ε) (qOf ε) : ℝ))
          (2 * ((qOf ε : ℝ) - 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) ≤ hNeed ε := by
      unfold hNeed
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hp, hq] at h3
    have hmin : (min ((k + r : ℕ) : ℝ) ((r + 1 : ℕ) : ℝ)) = (r : ℝ) + 1 := by
      rw [min_eq_right]
      · push_cast; ring
      · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        push_cast
        linarith
    have hr1 : ((r + 1 : ℕ) : ℝ) - 1 = (r : ℝ) := by push_cast; ring
    rw [hmin, hr1] at h3
    set M := max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * ((r : ℝ) + 1)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2)
      with hM
    have hM1 : 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ M := le_max_right _ _
    have h0 : 0 ≤ 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hM2 : 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * M + 1 := by linarith
    have hlt : 8 * Real.sqrt (2 * ((r : ℝ) + 1)) * (4 * M + 1) < h := lt_of_le_of_lt h3 hgap.2.2
    rw [ha, hq0', lt_div_iff₀ (by positivity)]
    unfold S0.bS S0.nS
    calc 2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * (8 * Real.sqrt (2 * ((r : ℝ) + 1)))
        ≤ (4 * M + 1) * (8 * Real.sqrt (2 * ((r : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right hM2 (by positivity)
      _ = 8 * Real.sqrt (2 * ((r : ℝ) + 1)) * (4 * M + 1) := by ring
      _ < h := hlt
  have ha0 : 0 ≤ a := by
    have : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity
    linarith
  have hI := hIS k r z μW μN hz hT hW hN x₀ hx₀ x hx a hb
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hWae : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by
    rw [ae_iff]; simpa using hW.2.2.1
  have hNae : ∀ᵐ y ∂μN, Matrix.of y ∈ Nset k r := by
    rw [ae_iff]; simpa using hN.2.2.1
  have hpae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  refine Integrable.mono' (hI.const_mul (C * c0 ^ (-a) * ‖ξ‖))
    (integrand_aesm T hμ hP ⟨hz, hT, hc, hπ, hW, hN⟩ v₁ v₂ ξ hx₀ hx) ?_
  filter_upwards [hpae] with p hp'
  have hgU : x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x) ∈ UH (Hpk k r) :=
    Transport.uh_mul (Transport.uh_facts hP hx₀).2.1
      (Transport.uh_mul (Transport.uh_mul hp'.1.1 hp'.2.1) hx)
  set g := x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x) with hg
  have hgJ := (Transport.uh_facts hP hgU).2.2
  have hCg := hC (P * g * P⁻¹) hgJ
  have hgN : 1 ≤ Formalism.FourierDecayAlt.B.gN g := S0.Dec.one_le_gN k r g hgU
  have hfr : c0 * Formalism.FourierDecayAlt.B.gN g ≤ frob (P * g * P⁻¹) := hcg g
  have hpos : 0 < c0 * Formalism.FourierDecayAlt.B.gN g := mul_pos hc0 (by linarith)
  have hfrpos : 0 < frob (P * g * P⁻¹) := lt_of_lt_of_le hpos hfr
  have hpow : frob (P * g * P⁻¹) ^ (-a) ≤ c0 ^ (-a) * Formalism.FourierDecayAlt.B.gN g ^ (-a) := by
    rw [← Real.mul_rpow hc0.le (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos hpos hfr (by linarith)
  have hC0 : 0 ≤ C := by
    have hX : 0 < frob (P * g * P⁻¹) ^ (-a) := Real.rpow_pos_of_pos hfrpos _
    have := le_trans (norm_nonneg _) hCg
    exact (mul_nonneg_iff_of_pos_right hX).mp this
  have hcoef : ‖psiCoef T μ P v₁ v₂ g‖ ≤ C * (c0 ^ (-a) * Formalism.FourierDecayAlt.B.gN g ^ (-a)) :=
    le_trans hCg (mul_le_mul_of_nonneg_left hpow hC0)
  have hchi : ‖chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ‖ = ‖ξ‖ := by
    unfold chiInv Formalism.MainNotions.S.psiGen
    rw [norm_smul, norm_star, Complex.norm_exp_I_mul_ofReal, one_mul,
      pi_isometry hz hT hπ _ ((Transport.uw_closedSubgroup k r z).inv_mem _ hp'.1)]
  rw [norm_smul, hchi]
  calc ‖psiCoef T μ P v₁ v₂ g‖ * ‖ξ‖ ≤ C * (c0 ^ (-a) * Formalism.FourierDecayAlt.B.gN g ^ (-a)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = C * c0 ^ (-a) * ‖ξ‖ * Formalism.FourierDecayAlt.B.gN g ^ (-a) := by ring

theorem intCoef_of (hIS : S0.IntSStatement) (hDD : DecDerivStatement) : Transport.IntCoefStatement := by
  intro k r hk ε lam h hgap u Vp _ _ _ T μ hμ P hP z c π μW μN hB v₁ v₂ ξ x₀ x hx₀ hx
  exact integrable_coef_of hIS hDD hk hgap T hμ hP hB v₁ v₂ ξ hx₀ hx

theorem transport_of (hIS : S0.IntSStatement) (hDD : DecDerivStatement) {k r : ℕ} (hk : 1 ≤ k)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {u : Fin k → ℝ} {h : ℝ}
    (hgap : GapLap ε lam h) : BesselNZ ε lam u → BesselAll ε lam u :=
  Transport.transport (intCoef_of hIS hDD) hk hgap

end TransportInt

end ReciprocityTheory.ChartRestriction.DS.Lap
