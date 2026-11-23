import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix MeasureTheory Filter Topology Set Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.CutDeriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_of : Continuous fun y : PI.MtM n => (Matrix.of y : Mat n) := continuous_id

theorem continuous_scale (c : ℝ) : Continuous fun y : PI.MtM n => (c • Matrix.of y : Mat n) :=
  continuous_of.const_smul c

theorem notMem_tsupport {ρ : Mat n → ℝ} {R : ℝ} (hR : 0 < R) (X : Mat n) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    {y : PI.MtM n}
    (hy : y ∉ (fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) :
    ex X (-t) * (R⁻¹ • Matrix.of y) ∉ tsupport ρ := fun hs =>
  hy ⟨(t, ex X (-t) * (R⁻¹ • Matrix.of y)), ⟨ht, hs⟩, by
    simp only
    rw [← Matrix.mul_assoc, ← ex_add, add_neg_cancel, ex_zero, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hR.ne', one_smul]
    rfl⟩

theorem isCompact_img {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) (R : ℝ) (X : Mat n) {T : Set ℝ}
    (hT : IsCompact T) : IsCompact
      ((fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) := by
  have h1 : Continuous fun p : ℝ × Mat n => (R • (ex X p.1 * p.2) : Mat n) :=
    (((continuous_ex X).comp continuous_fst).matrix_mul continuous_snd).const_smul R
  exact (hT.prod hc.isCompact).image h1

theorem hasCompactSupport_coef {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) {R : ℝ} (hR : 0 < R)
    (φ : PI.MtM n → ℂ) : HasCompactSupport fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * φ y := by
  refine HasCompactSupport.intro (isCompact_img hc R 0 (isCompact_singleton (x := (0 : ℝ)))) fun y hy => ?_
  have := notMem_tsupport hR 0 (mem_singleton _) hy
  rw [neg_zero, ex_zero, Matrix.one_mul] at this
  rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

theorem continuous_coef {ρ : Mat n → ℝ} (hρ : Continuous ρ) (R : ℝ) {F : Mat n → H} (hF : Continuous F) (v : H) :
    Continuous fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ :=
  (Complex.continuous_ofReal.comp (hρ.comp (continuous_scale _))).mul
    ((hF.comp continuous_of).inner continuous_const)

variable {Hm : Mat n} {σ : Mat n → (H →L[ℂ] H)} {μ : Measure (PI.MtM n)} {w : H} {F : Mat n → H}

theorem cutI_eq (hμ : PI.IsHaarOnM (UH Hm) μ) (hFw : ∀ a ∈ UH Hm, F a = σ a w) (R : ℝ) (ρ : Mat n → ℝ) (v : H) :
    cutI σ μ w R ρ v =
      ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y) ∂μ := by
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  rw [hFw _ hg, inner_conj_symm]

theorem inner_iso (h : URep Hm σ) {g : Mat n} (hg : g ∈ UH Hm) (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (h.iso g hg)).inner_map_map x y

variable [CompleteSpace H]

theorem apply_cutI (h : URep Hm σ) (hμ : PI.IsHaarOnM (UH Hm) μ) (hF : Continuous F)
    (hFw : ∀ a ∈ UH Hm, F a = σ a w) {R : ℝ} (hR : 0 < R) {ρ : Mat n → ℝ} (hρ : Continuous ρ)
    (hc : HasCompactSupport ρ) (v : H) {X : Mat n} (hX : ∀ t, ex X t ∈ UH Hm) (t : ℝ) :
    σ (ex X t) (cutI σ μ w R ρ v) =
      ∫ y : PI.MtM n, ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
        F (Matrix.of y) ∂μ := by
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hK => CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact h.grp hμ hK⟩
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  have hi : Integrable (fun y : PI.MtM n =>
      ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y)) μ :=
    ((continuous_coef hρ R hF v).smul (hF.comp continuous_of)).integrable_of_hasCompactSupport
      (hasCompactSupport_coef hc hR _).smul_right
  have hl : Continuous (PI.lmulQ (ex X t)) := by
    have : Continuous fun y : PI.MtM n => (ex X t * Matrix.of y : Mat n) :=
      continuous_const.matrix_mul continuous_of
    exact this
  have hg : Continuous fun y : PI.MtM n =>
      ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) • F (Matrix.of y) :=
    ((Complex.continuous_ofReal.comp (hρ.comp (continuous_const.matrix_mul (continuous_scale _)))).mul
      ((hF.comp continuous_of).inner continuous_const)).smul (hF.comp continuous_of)
  rw [cutI_eq hμ hFw, ← (σ (ex X t)).integral_comp_comm hi]
  conv_rhs => rw [← hμ.2.2.2 _ (hX t)]
  rw [integral_map hl.measurable.aemeasurable hg.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  have e : (Matrix.of (PI.lmulQ (ex X t) g) : Mat n) = ex X t * Matrix.of g := rfl
  rw [e, hFw _ (h.rep.mul_mem _ (hX t) _ hg), h.rep.apply_mul (hX t) hg, inner_iso h (hX t), map_smul,
    hFw _ hg, Matrix.mul_smul, ← Matrix.mul_assoc, ← ex_add, neg_add_cancel, ex_zero, Matrix.one_mul]

theorem cutDer : CutDer := by
  intro n Hm H _ _ _ σ h μ hμ w hw R hR ρ hρ hc v hv
  haveI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun _ hK => CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact h.grp hμ hK⟩
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  obtain ⟨F, hF, hFw⟩ := SmOn.exists_contDiff hw h.grp.1
  have hFc : Continuous F := hF.continuous
  have hFo : Continuous fun y : PI.MtM n => F (Matrix.of y) := hFc.comp continuous_of
  refine ⟨?_, fun X hX' => ?_⟩
  · have h1 := isSm_integral h.grp h.rep hw hμ (continuous_coef hρ.continuous R hFc v)
      (hasCompactSupport_coef hc hR _)
    convert h1 using 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with g hg
    rw [hFw _ hg, inner_conj_symm]
  have hX : ∀ t, ex X t ∈ UH Hm := fun t => ex_mem_of_lie hX' t
  have hdv : IsSm (UH Hm) σ (ds σ X v) :=
    hv.dsW h.rep (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  have hu : Continuous fun t => σ (ex X t) v :=
    continuous_iff_continuousAt.2 fun t => (hv.hasDerivAt h.rep hX t).continuousAt
  have hu' : Continuous fun t => σ (ex X t) (ds σ X v) :=
    continuous_iff_continuousAt.2 fun t => (hdv.hasDerivAt h.rep hX t).continuousAt
  have hγ : Continuous fun p : ℝ × PI.MtM n => ex X (-p.1) * (R⁻¹ • Matrix.of p.2 : Mat n) :=
    ((continuous_ex X).comp continuous_fst.neg).matrix_mul ((continuous_scale _).comp continuous_snd)
  have hρL := (contDiff_Lx X hρ).continuous
  have hcL : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
  have hc1 : ∀ {ψ : Mat n → ℝ} {u : ℝ → H}, Continuous ψ → Continuous u →
      Continuous fun p : ℝ × PI.MtM n =>
        (ψ (ex X (-p.1) * (R⁻¹ • Matrix.of p.2 : Mat n)) : ℂ) * ⟪F (Matrix.of p.2), u p.1⟫_ℂ :=
    fun hψ hu => (Complex.continuous_ofReal.comp (hψ.comp hγ)).mul
      ((hFo.comp continuous_snd).inner (hu.comp continuous_fst))
  have hd := hasDerivAt_integral_cpt (μ := μ)
    (F := fun t y => ((ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ) •
      F (Matrix.of y))
    (F' := fun t y => ((Lx X ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) v⟫_ℂ +
      (ρ (ex X (-t) * (R⁻¹ • Matrix.of y)) : ℂ) * ⟪F (Matrix.of y), σ (ex X t) (ds σ X v)⟫_ℂ) •
      F (Matrix.of y))
    (fun t => ((hc1 hρ.continuous hu).comp (Continuous.prodMk_right t)).smul hFo)
    (((hc1 hρL hu).add (hc1 hρ.continuous hu')).smul (hFo.comp continuous_snd))
    (fun t a => by
      have d1 := (hasDerivAt_Lx X (R⁻¹ • Matrix.of a) hρ t).ofReal_comp
      have d2 : HasDerivAt (fun s => ⟪F (Matrix.of a), σ (ex X s) v⟫_ℂ)
          ⟪F (Matrix.of a), σ (ex X t) (ds σ X v)⟫_ℂ t :=
        ((innerSL ℂ (F (Matrix.of a))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
          (hv.hasDerivAt h.rep hX t)
      exact (d1.mul d2).smul_const _)
    (isCompact_img hc R X (isCompact_Icc (a := (-1 : ℝ)) (b := 1)))
    (fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport (notMem_tsupport hR X (t := 0) (by norm_num) ha),
        Complex.ofReal_zero, zero_mul, zero_smul])
    (fun t ht a ha => by
      have h0 := notMem_tsupport hR X ht ha
      rw [image_eq_zero_of_notMem_tsupport h0,
        image_eq_zero_of_notMem_tsupport (fun hs => h0 (tsupport_Lx X ρ hs)),
        Complex.ofReal_zero, zero_mul, zero_mul, add_zero, zero_smul])
  have hi : ∀ {ψ : Mat n → ℝ} (u : H), Continuous ψ → HasCompactSupport ψ → Integrable (fun y : PI.MtM n =>
      ((ψ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), u⟫_ℂ) • F (Matrix.of y)) μ := fun u hψ hcψ =>
    ((continuous_coef hψ R hFc u).smul hFo).integrable_of_hasCompactSupport
      (hasCompactSupport_coef hcψ hR _).smul_right
  rw [cutI_eq hμ hFw R (Lx X ρ), cutI_eq hμ hFw R ρ (ds σ X v),
    ← integral_add (hi _ hρL hcL) (hi _ hρ.continuous hc)]
  conv_lhs => unfold ds
  simp_rw [apply_cutI h hμ hFc hFw hR hρ.continuous hc v hX]
  rw [hd.deriv]
  simp only [neg_zero, ex_zero, Matrix.one_mul, h.rep.map_one, ContinuousLinearMap.one_apply, add_smul]

end GlobalTheory.CompanionTheory.CutDeriv

end
