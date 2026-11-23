import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.AnnihilatorDuality

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {n : ℕ} {ψ : AddChar (AF F) ℂ}
  {v : HeightOneSpectrum (𝓞 F)} {μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)} {νv : Measure (HermR (Fv F v) σ n)}
  {Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ}

theorem uu_eq (T b : HermR (Fv F v) σ n) :
    uu σ J ψ v μv Φv T b =
      ∫ Y, Φv Y * psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) ∂μv := by
  unfold uu jtR
  rw [← integral_mul_const]
  congr 1; funext Y
  rw [mul_assoc, ← psiV_add, trPair_sub_right, trPair_comm (Fv F v) T.1 b.1, sub_eq_add_neg]

theorem psiV_trPair_add_left (ψ : AddChar (AF F) ℂ) (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (b b' : HermR (Fv F v) σ n) :
    psiV F ψ v (trPair (Fv F v) (b + b').1 S) = psiV F ψ v (trPair (Fv F v) b.1 S) * psiV F ψ v (trPair (Fv F v) b'.1 S) := by
  rw [← psiV_add, ← trPair_add_left]; rfl

variable {lam : Measure (Fin n → Fv F v ⊗[F] E)} {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)}
  {g : HermR (Fv F v) σ n → ℂ} {T : HermR (Fv F v) σ n}

def setP (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (HermR (Fv F v) σ n)) (T : HermR (Fv F v) σ n) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Y | ∀ b ∈ Λ, psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1}

theorem isClosed_setP (hψ : IsCharAF F ψ) (Λ : Set (HermR (Fv F v) σ n)) (T : HermR (Fv F v) σ n) :
    IsClosed (setP σ J ψ v Λ T) := by
  have : setP σ J ψ v Λ T = ⋂ b ∈ Λ, {Y | psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1} := by
    ext Y; simp [setP]
  rw [this]
  exact isClosed_biInter fun b _ => isClosed_eq ((continuous_psiV hψ).comp
    (continuous_trPair continuous_const ((continuous_gramR' σ J).sub continuous_const))) continuous_const

theorem setIntegral_uu (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (R : ℝ) (hR : 0 < R) :
    ∫ b in (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv =
      ((νv.real (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) *
        ∫ Y in setP σ J ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) T, Φv Y ∂μv := by
  have := h.sdH.1
  have := h.sdW.1
  set Λ := ballH v σ n R hR.le with hΛdef
  have hΛc : IsCompact (Λ : Set (HermR (Fv F v) σ n)) := isCompact_ballH v σ n R hR.le
  have hΛm : MeasurableSet (Λ : Set (HermR (Fv F v) σ n)) := hΛc.isClosed.measurableSet
  have hfin : νv (Λ : Set (HermR (Fv F v) σ n)) < ⊤ := hΛc.measure_lt_top
  haveI : IsFiniteMeasure (νv.restrict (Λ : Set (HermR (Fv F v) σ n))) := isFiniteMeasure_restrict.2 hfin.ne
  let f : HermR (Fv F v) σ n → (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun b Y => Φv Y * psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1))
  have hΦc : Continuous Φv := h.sb.1.continuous
  have hΦi : Integrable Φv μv := hΦc.integrable_of_hasCompactSupport h.sb.2
  have hψc := continuous_psiV (v := v) h.chr
  have hfc : Continuous (Function.uncurry f) :=
    (hΦc.comp continuous_snd).mul (hψc.comp (continuous_trPair (continuous_subtype_val.comp continuous_fst)
      (((continuous_gramR' σ J).comp continuous_snd).sub continuous_const)))
  have hint : Integrable (Function.uncurry f) ((νv.restrict (Λ : Set (HermR (Fv F v) σ n))).prod μv) := by
    refine Integrable.mono' ((integrable_const (1 : ℂ)).mul_prod hΦi).norm hfc.aestronglyMeasurable ?_
    filter_upwards with p
    simp [f, Function.uncurry, norm_psiV h.chr]
  have hPm : MeasurableSet (setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T) :=
    (isClosed_setP h.chr _ T).measurableSet
  calc ∫ b in (Λ : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv
      = ∫ b in (Λ : Set (HermR (Fv F v) σ n)), ∫ Y, f b Y ∂μv ∂νv := by
        congr 1; funext b; exact uu_eq T b
    _ = ∫ Y, ∫ b in (Λ : Set (HermR (Fv F v) σ n)), f b Y ∂νv ∂μv := integral_integral_swap hint
    _ = ∫ Y, ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) *
          (setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T).indicator Φv Y ∂μv := by
        congr 1; funext Y
        simp only [f]
        rw [integral_const_mul, setIntegral_char_subgroup νv Λ hΛm
          (fun b => psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)))
          (fun b b' => psiV_trPair_add_left ψ _ b b')]
        by_cases hP : ∀ b ∈ Λ, psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1
        · rw [if_pos hP, Set.indicator_of_mem (show Y ∈ setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T from
            fun b hb => hP b hb)]
          ring
        · rw [if_neg hP, Set.indicator_of_notMem (show Y ∉ setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T from
            fun h' => hP fun b hb => h' b hb)]
          ring
    _ = ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) *
          ∫ Y in setP σ J ψ v (Λ : Set (HermR (Fv F v) σ n)) T, Φv Y ∂μv := by
        rw [integral_const_mul, integral_indicator hPm]

def perpH (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (HermR (Fv F v) σ n)) :
    Set (HermR (Fv F v) σ n) :=
  {D | ∀ b ∈ Λ, psiV F ψ v (trPair (Fv F v) b.1 D.1) = 1}

theorem isClosed_perpH (hψ : IsCharAF F ψ) (Λ : Set (HermR (Fv F v) σ n)) : IsClosed (perpH σ ψ v Λ) := by
  have : perpH σ ψ v Λ = ⋂ b ∈ Λ, {D : HermR (Fv F v) σ n | psiV F ψ v (trPair (Fv F v) b.1 D.1) = 1} := by
    ext D; simp [perpH]
  rw [this]
  exact isClosed_biInter fun b _ => isClosed_eq ((continuous_psiV hψ).comp
    (continuous_trPair continuous_const continuous_subtype_val)) continuous_const

theorem perpH_subset {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hperp : ∀ R : ℝ, 0 < R → ∀ D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), D ∈ HermR (Fv F v) σ n →
      (∀ b : HermR (Fv F v) σ n, nM v b.1 ≤ R → psiV F ψ v (trPair (Fv F v) b.1 D) = 1) → nM v D ≤ C₀ / R)
    (R : ℝ) (hR : 0 < R) :
    perpH σ ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) ⊆
      (ballH v σ n (C₀ / R) (div_nonneg hC₀ hR.le) : Set (HermR (Fv F v) σ n)) :=
  fun D hD => hperp R hR D.1 D.2 (fun b hb => hD b hb)

theorem isCompact_perpH (hψ : IsCharAF F ψ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hperp : ∀ R : ℝ, 0 < R → ∀ D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), D ∈ HermR (Fv F v) σ n →
      (∀ b : HermR (Fv F v) σ n, nM v b.1 ≤ R → psiV F ψ v (trPair (Fv F v) b.1 D) = 1) → nM v D ≤ C₀ / R)
    (R : ℝ) (hR : 0 < R) : IsCompact (perpH σ ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n))) :=
  (isCompact_ballH v σ n (C₀ / R) (div_nonneg hC₀ hR.le)).of_isClosed_subset (isClosed_perpH hψ _)
    (perpH_subset hC₀ hperp R hR)

theorem vol_mul_vol_perp (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (R : ℝ) (hR : 0 < R) :
    νv.real (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n)) *
      νv.real (perpH σ ψ v (ballH v σ n R hR.le : Set (HermR (Fv F v) σ n))) = 1 := by
  have := h.sdH.1
  obtain ⟨C₀, hC₀, hperp⟩ := perp_bound v σ h.cm h.chr n
  set Λ := ballH v σ n R hR.le with hΛdef
  have hΛc : IsCompact (Λ : Set (HermR (Fv F v) σ n)) := isCompact_ballH v σ n R hR.le
  have hΛo : IsOpen (Λ : Set (HermR (Fv F v) σ n)) := isOpen_ballH v σ n R hR
  have hΛm : MeasurableSet (Λ : Set (HermR (Fv F v) σ n)) := hΛc.isClosed.measurableSet
  have hPc : IsCompact (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))) := isCompact_perpH h.chr hC₀ hperp R hR
  have hPm : MeasurableSet (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))) := hPc.isClosed.measurableSet
  let Φ0 : HermR (Fv F v) σ n → ℂ := (Λ : Set (HermR (Fv F v) σ n)).indicator (fun _ => 1)
  have hΦ0c : Continuous Φ0 := IsClopen.continuous_indicator ⟨hΛc.isClosed, hΛo⟩ continuous_const
  have hΦ0s : HasCompactSupport Φ0 := HasCompactSupport.intro hΛc (fun x hx => Set.indicator_of_notMem hx _)
  have hhat : (fun y => ∫ x, Φ0 x * psiV F ψ v (pairHerm (Fv F v) σ n x y) ∂νv) =
      (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))).indicator
        (fun _ => ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ)) := by
    funext y
    have e1 : ∫ x, Φ0 x * psiV F ψ v (pairHerm (Fv F v) σ n x y) ∂νv =
        ∫ x in (Λ : Set (HermR (Fv F v) σ n)), psiV F ψ v (trPair (Fv F v) x.1 y.1) ∂νv := by
      rw [← integral_indicator hΛm]
      congr 1; funext x
      simp only [Φ0]
      by_cases hx : x ∈ (Λ : Set (HermR (Fv F v) σ n))
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    rw [e1, setIntegral_char_subgroup νv Λ hΛm (fun x => psiV F ψ v (trPair (Fv F v) x.1 y.1))
      (fun b b' => psiV_trPair_add_left ψ y.1 b b')]
    by_cases hy : ∀ x ∈ Λ, psiV F ψ v (trPair (Fv F v) x.1 y.1) = 1
    · rw [if_pos hy, Set.indicator_of_mem (show y ∈ perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n)) from
        fun b hb => hy b hb)]
    · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n)) from
        fun h' => hy fun b hb => h' b hb)]
  have hint : Integrable (fun y => ∫ x, Φ0 x * psiV F ψ v (pairHerm (Fv F v) σ n x y) ∂νv) νv := by
    rw [hhat]
    exact (integrable_indicator_iff hPm).2 (integrableOn_const hPc.measure_lt_top.ne)
  have key := h.sdH.2 Φ0 hΦ0c hΦ0s hint 0
  have hhat' := congrFun hhat
  simp only [] at key hhat'
  simp only [hhat'] at key
  have h0 : ∀ y : HermR (Fv F v) σ n, psiV F ψ v (pairHerm (Fv F v) σ n y 0) = 1 := by
    intro y
    show psiV F ψ v (trPair (Fv F v) y.1 (0 : HermR (Fv F v) σ n).1) = 1
    rw [AddSubgroup.coe_zero, trPair_zero_right, psiV_zero]
  simp only [h0, mul_one, neg_zero] at key
  have hΦ00 : Φ0 0 = 1 := by
    simp only [Φ0]
    exact Set.indicator_of_mem (show (0 : HermR (Fv F v) σ n) ∈ (Λ : Set (HermR (Fv F v) σ n)) from Λ.zero_mem) _
  rw [integral_indicator hPm, setIntegral_const, hΦ00] at key
  have key' : ((νv.real (perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n))) * νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_mul]; simpa [Complex.real_smul] using key
  rw [mul_comm]
  exact_mod_cast key'

theorem setP_eq (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (Λ : Set (HermR (Fv F v) σ n)) :
    setP σ J ψ v Λ T =
      gramR (Fv F v) σ J ⁻¹' (Subtype.val '' {S : HermR (Fv F v) σ n | S - T ∈ perpH σ ψ v Λ}) := by
  have hσ : ∀ x, σ (σ x) = x := sigma_invol' σ h.cm.2.2.2
  ext Y
  constructor
  · intro hY
    exact ⟨⟨gramR (Fv F v) σ J Y, gramR_mem' (Fv F v) σ hσ J h.herm.1 Y⟩, fun b hb => hY b hb, rfl⟩
  · rintro ⟨S, hS, hSY⟩ b hb
    have h1 := hS b hb
    show psiV F ψ v (trPair (Fv F v) b.1 (gramR (Fv F v) σ J Y - T.1)) = 1
    rw [← hSY]
    exact h1

end PositivityTheory.SiegelWeilFormula.SwLocFin.DualA

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
  PositivityTheory.SiegelWeilFormula.SwLocFin.DualA
open scoped TensorProduct Matrix

theorem dualP : DualP := by
  intro F E _ _ _ _ _ σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
  have := h.sdH.1
  obtain ⟨C₀, hC₀, hperp⟩ := perp_bound v σ h.cm h.chr n
  set B := {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} with hBdef
  have hBo : IsOpen B := isOpen_unitHerm' σ n
  have hTB : T ∈ B := h.unit
  have hgc : ContinuousAt g T := (h.dens.1).continuousAt (hBo.mem_nhds hTB)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hU : {S | S ∈ B ∧ g S ∈ Metric.ball (g T) (ε / 2)} ∈ 𝓝 T :=
    Filter.inter_mem (hBo.mem_nhds hTB) (hgc.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε)))
  obtain ⟨r, hr, hsub⟩ := exists_ballH_sub hU
  refine ⟨max 1 (C₀ / r), fun R hR => ?_⟩
  have hR1 : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hR)
  have hCr : C₀ / R ≤ r := by
    rw [div_le_iff₀ hR1]
    have := (div_le_iff₀ hr).1 (le_trans (le_max_right _ _) hR)
    linarith
  set Λ := ballH v σ n R hR1.le with hΛdef
  set P := perpH σ ψ v (Λ : Set (HermR (Fv F v) σ n)) with hPdef
  set C := {S : HermR (Fv F v) σ n | S - T ∈ P} with hCdef
  have hCsub : ∀ S ∈ C, S ∈ B ∧ g S ∈ Metric.ball (g T) (ε / 2) := fun S hS =>
    hsub S ((perpH_subset hC₀ hperp R hR1 hS).trans hCr)
  have hPc : IsCompact P := isCompact_perpH h.chr hC₀ hperp R hR1
  have hCc : IsCompact C := by
    have : C = (fun S => S - T) ⁻¹' P := rfl
    rw [this]; exact (Homeomorph.subRight T).isCompact_preimage.2 hPc
  have hνC : νv.real C = νv.real P := by
    have : C = (fun S => S + (-T)) ⁻¹' P := by ext S; simp [C, sub_eq_add_neg]
    simp only [Measure.real]
    rw [this, measure_preimage_add_right]
  have hvol : νv.real (Λ : Set (HermR (Fv F v) σ n)) * νv.real P = 1 := vol_mul_vol_perp h R hR1
  have hdens := h.dens.2 C hCc (fun S hS => (hCsub S hS).1)
  have hval : ∫ b in (Λ : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv =
      ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) * ∫ b in C, g b ∂νv := by
    rw [setIntegral_uu h R hR1, setP_eq h, hdens]
  have hgi : IntegrableOn g C νv :=
    (h.dens.1.mono (fun S hS => (hCsub S hS).1)).integrableOn_compact hCc
  have hci : IntegrableOn (fun _ => g T) C νv := integrableOn_const hCc.measure_lt_top.ne
  have hdiff : ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) * ∫ b in C, g b ∂νv - g T =
      ((νv.real (Λ : Set (HermR (Fv F v) σ n)) : ℝ) : ℂ) * ∫ b in C, (g b - g T) ∂νv := by
    rw [integral_sub hgi hci, setIntegral_const, mul_sub, hνC, Complex.real_smul, ← mul_assoc,
      ← Complex.ofReal_mul, hvol, Complex.ofReal_one, one_mul]
  have hbound : ‖∫ b in C, (g b - g T) ∂νv‖ ≤ ε / 2 * νv.real C := by
    refine norm_setIntegral_le_of_norm_le_const hCc.measure_lt_top (fun S hS => ?_)
    have := (hCsub S hS).2
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm]
  show ‖∫ b in (Λ : Set (HermR (Fv F v) σ n)), uu σ J ψ v μv Φv T b ∂νv - g T‖ < ε
  rw [hval, hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg measureReal_nonneg]
  calc νv.real (Λ : Set (HermR (Fv F v) σ n)) * ‖∫ b in C, (g b - g T) ∂νv‖
      ≤ νv.real (Λ : Set (HermR (Fv F v) σ n)) * (ε / 2 * νv.real C) :=
        mul_le_mul_of_nonneg_left hbound measureReal_nonneg
    _ = ε / 2 * (νv.real (Λ : Set (HermR (Fv F v) σ n)) * νv.real P) := by rw [hνC]; ring
    _ = ε / 2 := by rw [hvol, mul_one]
    _ < ε := half_lt_self hε

end PositivityTheory.SiegelWeilFormula.SwLocFin
