import Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
import Development.WeilBound.ThetaLifts.LatticeBasics.BotAsm
import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseUnfoldB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseKPair

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
private theorem zero_of_half_pk {U : Set ℂ} (hU : IsOpen U) (hd : ∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ {z | τ < z.re})) {t : ℝ} (ht : ∀ z : ℂ, t < z.re → z ∈ U ∧ f z = 0) {s : ℂ} (hs : s ∈ U)
    (hs' : τ < s.re) : f s = 0 := by
  have hsh : Continuous fun z : ℂ => z + (τ : ℂ) := by fun_prop
  have key := eq_zero_of_right (U := (fun z : ℂ => z + (τ : ℂ)) ⁻¹' U) (hU.preimage hsh)
    (fun z => by
      have tt : Tendsto (fun z : ℂ => z + (τ : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + (τ : ℂ))) :=
        tendsto_nhdsWithin_iff.2 ⟨hsh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun w hw h => hw (add_right_cancel h)⟩
      exact tt.eventually (hd _))
    (f := fun z => f (z + (τ : ℂ)))
    (hf.comp (by fun_prop) fun z hz => ⟨hz.1, by simpa using hz.2⟩)
    (t := t - τ) (fun z hz => ⟨(ht _ (by simp; linarith [show t - τ < z.re from hz])).1,
      (ht _ (by simp; linarith [show t - τ < z.re from hz])).2⟩)
    (s := s - (τ : ℂ)) (by simpa using hs) (by simpa using hs')
  simpa using key
private theorem cpow_integral_pk {Y : Type} [MeasurableSpace Y] {μ : Measure Y} {A : Y → ℝ} {b : Y → ℂ} {t₀ q C : ℝ}
    (h0 : ∀ x, 0 < A x) (mA : Measurable A) (mb : AEStronglyMeasurable b μ) (hb : ∀ x, ‖b x‖ ≤ C * A x ^ q)
    (hi : ∀ t, t₀ ≤ t → Integrable (fun x => A x ^ t) μ) (s₀ : ℂ) :
    (∀ z : ℂ, t₀ < z.re - s₀.re + q → Integrable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ) ∧
      DifferentiableOn ℂ (fun z => ∫ x, (A x : ℂ) ^ (z - s₀) * b x ∂μ) {z : ℂ | t₀ < z.re - s₀.re + q} := by
  have mz : ∀ z : ℂ, AEStronglyMeasurable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ := fun z =>
    ((Complex.measurable_ofReal.comp mA).pow_const _).aestronglyMeasurable.mul mb
  have nz : ∀ (z : ℂ) x, ‖(A x : ℂ) ^ (z - s₀) * b x‖ ≤ |C| * A x ^ (z.re - s₀.re + q) := fun z x => by
    have p := h0 x
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos p, Complex.sub_re, Real.rpow_add p, mul_left_comm]
    exact mul_le_mul_of_nonneg_left ((hb x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg p.le _)))
      (Real.rpow_nonneg p.le _)
  refine ⟨fun z hz => ((hi _ hz.le).const_mul |C|).mono' (mz z) (.of_forall (nz z)), ?_⟩
  refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound
    (isOpen_lt continuous_const (by fun_prop)) (fun x z _ => ?_) (fun z _ => mz z) fun z hz => ?_
  · have : (A x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h0 x).ne'
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl this)).mul_const _ |>.differentiableWithinAt
  · have hz' : t₀ < z.re - s₀.re + q := hz
    set u := z.re - s₀.re + q with hu
    refine ⟨(u - t₀) / 2, by linarith, fun w hw => ?_, fun x => |C| * (A x ^ (u - (u - t₀) / 2) + A x ^ (u + (u - t₀) / 2)),
      (((hi _ (by linarith)).add (hi _ (by linarith))).const_mul _), fun w hw x => ?_⟩
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      show t₀ < w.re - s₀.re + q
      linarith [this.1]
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      refine (nz w x).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      have p := h0 x
      have p1 := Real.rpow_pos_of_pos p (u - (u - t₀) / 2)
      have p2 := Real.rpow_pos_of_pos p (u + (u - t₀) / 2)
      rcases le_total 1 (A x) with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h (show w.re - s₀.re + q ≤ u + (u - t₀) / 2 by linarith [this.2])
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge p h (show u - (u - t₀) / 2 ≤ w.re - s₀.re + q by linarith [this.1])
        linarith
private theorem coef_facts_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (hD : IsFundamentalDomain Γ D μ) [IsFiniteMeasure (μ.restrict D)] {φ : G → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ g, ‖φ g‖ ≤ C)
    (hi : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => pet μ D (fun y => φ (y * g)) φ) ∧ (∃ C' : ℝ, ∀ g, ‖pet μ D (fun y => φ (y * g)) φ‖ ≤ C') ∧
      ∀ g, pet μ D (fun y => φ (y * g⁻¹)) φ = star (pet μ D (fun y => φ (y * g)) φ) := by
  have C0 : 0 ≤ C := (norm_nonneg _).trans (hb 1)
  have nb : ∀ g y, ‖φ (y * g) * star (φ y)‖ ≤ C * C := fun g y => by
    rw [norm_mul, norm_star]; exact mul_le_mul (hb _) (hb _) (norm_nonneg _) C0
  have cm : ∀ g, Continuous fun y => φ (y * g) * star (φ y) := fun g => by fun_prop
  refine ⟨continuous_of_dominated (bound := fun _ => C * C) (fun g => (cm g).aestronglyMeasurable)
    (fun g => .of_forall (nb g)) (integrable_const _) (.of_forall fun y => by fun_prop), ⟨C * C * (μ.restrict D).real Set.univ, fun g => ?_⟩, fun g => ?_⟩
  · simpa [pet] using norm_integral_le_of_norm_le_const (μ := μ.restrict D) (.of_forall (nb g))
  · let f : G → ℂ := fun y => φ y * star (φ (y * g))
    have hf : ∀ (γ : Γ) x, f (γ • x) = f x := fun γ x => by
      simp only [f, Subgroup.smul_def, smul_eq_mul, mul_assoc]
      rw [hi _ γ.2, hi _ γ.2]
    have h2 : IsFundamentalDomain Γ (MulOpposite.op g⁻¹ • D) μ := hD.smul_of_comm (MulOpposite.op g⁻¹)
    have h3 : ∫ y in MulOpposite.op g⁻¹ • D, f y ∂μ = ∫ y in D, f (y * g⁻¹) ∂μ := by
      exact (measurePreserving_mul_right μ g⁻¹).setIntegral_image_emb (measurableEmbedding_mulRight g⁻¹) f D
    have h4 := h2.setIntegral_eq hD hf
    rw [h3] at h4
    simp only [pet]
    simp only [f, inv_mul_cancel_right] at h4
    rw [h4, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [mul_comm]
theorem _root_.UpperTheory.TP.rallis_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd K a e hK ha he t₀ hi hlt ν hν Φ hΦ φ hφ
  have h0 : min n 0 = 0 := by simp
  have h0' : min d 0 = 0 := by simp
  have cX := T.cpt F E σ B _ X _ _ hP.base (.inl hP.herm) h0
  have cW := T.cpt F E σ B _ W _ _ hP.base (.inr hP.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  have hKc := T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm) K hK
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hP.base (.inl hP.herm) h0
  obtain ⟨⟨K₁, a₁, hK₁, ha₁, ca, a0⟩, e₁, ce, he₁⟩ := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm)
  have eK : K₁ = K := Subgroup.ext fun k => (hK₁ k).trans (hK k).symm
  subst eK
  have ea : a₁ = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha₁.val p t hp k hk]
  subst ea
  have ee : e₁ = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he₁ x.1 x.2).trans (he x.1 x.2).symm))
  subst ee
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := cX.cnt; haveI := hP.good.haar; haveI := cX.right M.μ hP.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ hP.good.haar hP.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have s1 := T.polSch F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP Φ hΦ
  have bT := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP).1 Φ s1
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := T.dbl F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  have c2 : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 c0.ne'
  have sec := T.boxSec F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1 K₁ a₁ hK ha Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := T.swFull F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1
    K₁ a₁ hK ha μ D hμ hD Φ hΦ Φ hΦ
  set f : G2 σ X → ℂ := fun x => l (om₂ x (boxFun Φ (star Φ))) with hf
  set s₀ : ℂ := ((d : ℂ) - n) / 2 with hs₀
  have hap : ∀ g, a₁ (e₁ (1, g)) = a₁ (e₁ (g⁻¹, 1)) := fun g => by
    have := ha.mul (he g g).par (e₁ (g⁻¹, 1))
    rw [absE_det hJ, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    simpa using this
  have hi' : ∀ t, t₀ ≤ t → Integrable (fun g => a₁ (e₁ (1, g)) ^ t) M.μ := fun t ht => by
    have h1 : Integrable (fun g => (((a₁ (e₁ (1, g)) ^ t : ℝ) : ℂ))) M.μ := (hc1 _).1 (by
      simpa [hap] using (hi t ht).ofReal (𝕜 := ℂ))
    simpa using h1.re
  have idf : ∀ g, f (e₁ (1, g)) * detInv χW g = c' * coef om ν Φ g⁻¹ := fun g => by
    have h1 := Law.diag sec.law hJ he g (e₁ (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at h1
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat hP.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [h1, hf]
    simp only [e2]
    rw [hc _ (hP.weil.isUSplitting.pres _ _ s1) _ s1, coef]
  have cF : Continuous (coef om ν Φ) := by
    have h1 : coef om ν Φ = fun g => (c' : ℂ)⁻¹ * (f (e₁ (1, g⁻¹)) * detInv χW g⁻¹) := funext fun g => by
      rw [idf, inv_inv, inv_mul_cancel_left₀ c2]
    rw [h1]
    exact continuous_const.mul ((sec.cont.comp (ce.comp (continuous_const.prodMk continuous_inv))).mul
      ((continuous_detInv hP.hW).comp continuous_inv))
  obtain ⟨Cf, hCf⟩ := Law.bound sec.law sec.cont ha hKc
  have hre : (s₀ + (n : ℂ) / 2).re = (d : ℝ) / 2 := by
    have : s₀ + (n : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have bF : ∀ g, ‖coef om ν Φ g‖ ≤ (c'⁻¹ * Cf) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    have h1 := idf g⁻¹
    rw [inv_inv] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_detInv, mul_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg c0.le] at h2
    have h3 := hCf (e₁ (1, g⁻¹))
    rw [hre, hap, inv_inv, h2] at h3
    rw [mul_assoc, le_inv_mul_iff₀ c0]
    exact h3
  obtain ⟨Cφ, hCφ⟩ := cX.bdd hφ.1 hφ.2
  obtain ⟨cm, ⟨Cm, hCm⟩, im⟩ := coef_facts_pk hP.good.dom hφ.1 hCφ hφ.2
  change Continuous (mc M φ) at cm
  change ∀ g, ‖mc M φ g‖ ≤ Cm at hCm
  change ∀ g, mc M φ g⁻¹ = star (mc M φ g) at im
  have Cm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 1)
  have a0' : ∀ g, 0 < a₁ (e₁ (g, 1)) := fun g => a0 _
  have mA : Measurable fun g => a₁ (e₁ (g, 1)) :=
    (ca.comp (ce.comp (continuous_id.prodMk continuous_const))).measurable
  have hb : ∀ g, ‖coef om ν Φ g * star (mc M φ g)‖ ≤ (c'⁻¹ * Cf * Cm) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    rw [norm_mul, norm_star, mul_right_comm]
    exact mul_le_mul (bF g) (hCm g) (norm_nonneg _) ((norm_nonneg _).trans (bF g))
  obtain ⟨iZ, dZ⟩ := cpow_integral_pk a0' mA (cF.mul cm.star).aestronglyMeasurable hb hi s₀
  have hsr : s₀.re = ((d : ℝ) - n) / 2 := by
    have : s₀ = ((((d : ℝ) - n) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have ib : Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ := by
    simpa using iZ s₀ (by simpa using hlt)
  refine ⟨ib, fun L0 => ?_⟩
  obtain ⟨hol, t₁, far⟩ := _root_.GlobalTheory.ThK.Dbl.kpair_cont_k hP.base (.inl hP.herm) h0 cX hP.hW he ce hKc ha ca a0 sec.cont sec.law hE hP.good.haar hP.good.dom hi'
  have rp : IsRapid φ := cX.rapid hφ.1 hφ.2
  have eqP : ∀ z : ℂ, t₁ < z.re → kpair χW e₁ M.μ M.dom (Ê z) φ =
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ) := fun z hz => by
    have ez : ∀ g, flat a₁ f s₀ z (e₁ (1, g)) * detInv χW g * pet M.μ M.dom (fun h => φ (h * g)) φ =
        c' * ((a₁ (e₁ (g⁻¹, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g⁻¹ * star (mc M φ g⁻¹))) := fun g => by
      have h1 : star (mc M φ g⁻¹) = pet M.μ M.dom (fun h => φ (h * g)) φ := by rw [im, star_star]; rfl
      rw [h1, flat, hap, mul_assoc (_ ^ _), idf]
      ring
    rw [(far z hz).2.2 φ rp]
    simp only [ez]
    rw [(hc1 fun g => c' * ((a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)))).2, integral_const_mul]
  have H0 := zero_of_half_pk (τ := t₀ + s₀.re - (d : ℝ) / 2) hE.isOpen hE.disc
    (f := fun z => kpair χW e₁ M.μ M.dom (Ê z) φ -
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ))
    (((hol φ rp).mono Set.inter_subset_left).sub (((dZ.mono fun z hz => by
      have : t₀ + s₀.re - (d : ℝ) / 2 < z.re := hz.2
      show t₀ < z.re - s₀.re + (d : ℝ) / 2
      linarith).const_mul _).const_mul _))
    (t := t₁) (fun z hz => ⟨(far z hz).1, sub_eq_zero.2 (eqP z hz)⟩) u (by linarith)
  have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := bT.1.comp continuous_swap
  have key := An.at_value (φ := φ) (M.μ.restrict M.dom) (μ.restrict D)
    ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => bT.2.1 δ hδ γ hγ _ _⟩ ⟨hφ.1, Cφ, hCφ⟩
  have zl : ∀ h, ∫ g in M.dom, φ g * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
    have h1 : lift M om Φ φ h = 0 := congrFun L0 h
    have h2 : star (lift M om Φ φ h) = 0 := by rw [h1, star_zero]
    rw [← h2, lift, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp [mul_comm]
  simp only [zl, zero_mul, integral_zero] at key
  have hk : kpair χW e₁ M.μ M.dom (Ê s₀) φ = (if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) *
      ∫ y, (∫ h in D, theta om Φ y.1 h * star (theta om Φ y.2 h) ∂μ) * (φ y.2 * star (φ y.1)) ∂(M.μ.restrict M.dom).prod (M.μ.restrict M.dom) := by
    rw [kpair, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  have H1 : c * (c' * ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ) = 0 := by
    have h2 : kpair χW e₁ M.μ M.dom (Ê s₀) φ = 0 := by rw [hk, key, mul_zero]
    simpa [h2] using H0
  exact (mul_eq_zero.1 ((mul_eq_zero.1 H1).resolve_left c1)).resolve_left c2
end UpperTheory.TP
end
end
