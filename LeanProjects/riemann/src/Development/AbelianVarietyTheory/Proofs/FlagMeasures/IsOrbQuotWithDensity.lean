import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded

open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
open Formalism.FourierDecayAlt.P.Dx2.OrbJ

namespace GlobalTheory.ThA.QuotCut

private lemma continuous_of_symm_of_continuous {X : Type*} [TopologicalSpace X] {n : ℕ} {F : X → Matrix (Fin n) (Fin n) ℂ}
    (hF : Continuous F) : Continuous (fun y => (Matrix.of.symm (F y) : Fin n → Fin n → ℂ)) :=
  continuous_pi fun i => continuous_pi fun j => hF.matrix_elem i j

private lemma measurable_inv_apply_of_measurable_entries {n : ℕ} :
    Measurable (fun a : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of a)⁻¹) : Fin n → Fin n → ℂ)) := by
  have hc : Continuous (fun a : Fin n → Fin n → ℂ => Matrix.of a) := continuous_id
  have hdet : Measurable (fun a : Fin n → Fin n → ℂ => ((Matrix.of a).det)⁻¹) :=
    hc.matrix_det.measurable.inv
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have e : (fun a : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of a)⁻¹) : Fin n → Fin n → ℂ) i j)
      = fun a => ((Matrix.of a).det)⁻¹ * (Matrix.of a).adjugate i j := by
    funext a
    show ((Matrix.of a)⁻¹) i j = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact hdet.mul (hc.matrix_adjugate.matrix_elem i j).measurable

private lemma measurable_mul_apply_of_measurable_entries {n : ℕ} : Measurable (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
    (Matrix.of.symm (Matrix.of q.1 * Matrix.of q.2) : Fin n → Fin n → ℂ)) := by
  have h1 : Continuous (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.1) := continuous_fst
  have h2 : Continuous (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.2) := continuous_snd
  exact (continuous_of_symm_of_continuous (h1.matrix_mul h2)).measurable

private lemma measurable_actR_of {k r : ℕ} (x : B.Mat k r) :
    Measurable (fun q : Mt k r × B.SS k r => C6.actR x (Matrix.of q.1) q.2) := by
  have ha : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.1) := continuous_fst
  have h12 : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.2.1.2) := continuous_snd.fst.snd
  have h22 : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.2.2.2) := continuous_snd.snd.snd
  have hxi : Continuous (fun _ : Mt k r × B.SS k r => x⁻¹) := continuous_const
  have hxc : Continuous (fun _ : Mt k r × B.SS k r => x) := continuous_const
  have c1 := continuous_of_symm_of_continuous (ha.matrix_mul h12)
  have c2 := continuous_of_symm_of_continuous (((hxi.matrix_mul ha).matrix_mul hxc).matrix_mul h22)
  exact (((continuous_snd.fst.fst).prodMk c1).prodMk ((continuous_snd.snd.fst).prodMk c2)).measurable

private lemma actR_inv_actR {k r : ℕ} (x : B.Mat k r) (hx : IsUnit x.det) (A : B.Mat k r) (hA : IsUnit A.det)
    (q : B.SS k r) : C6.actR x A⁻¹ (C6.actR x A q) = q := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := q
  have e1 : A⁻¹ * (A * Matrix.of n) = Matrix.of n := Matrix.nonsing_inv_mul_cancel_left _ _ hA
  have e2 : x⁻¹ * A⁻¹ * x * (x⁻¹ * A * x * Matrix.of n') = Matrix.of n' := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.nonsing_inv_mul_cancel_left _ _ hA,
      Matrix.nonsing_inv_mul_cancel_left _ _ hx]
  show ((h, Matrix.of.symm (A⁻¹ * (A * Matrix.of n))),
      (h', Matrix.of.symm (x⁻¹ * A⁻¹ * x * (x⁻¹ * A * x * Matrix.of n')))) = ((h, n), (h', n'))
  rw [e1, e2]
  rfl

private lemma measurable_of_symm_of {n : ℕ} :
    Measurable fun a : Fin n → Fin n → ℂ => (Matrix.of.symm (Matrix.of a) : Fin n → Fin n → ℂ) :=
  measurable_id

private lemma measurable_of_symm_mul {α : Type*} [MeasurableSpace α] {n : ℕ} {F G : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : Measurable fun a => (Matrix.of.symm (F a) : Fin n → Fin n → ℂ))
    (hG : Measurable fun a => (Matrix.of.symm (G a) : Fin n → Fin n → ℂ)) :
    Measurable fun a => (Matrix.of.symm (F a * G a) : Fin n → Fin n → ℂ) := by
  have hFe : ∀ i l, Measurable fun a => F a i l := fun i l => measurable_pi_iff.mp (measurable_pi_iff.mp hF i) l
  have hGe : ∀ i l, Measurable fun a => G a i l := fun i l => measurable_pi_iff.mp (measurable_pi_iff.mp hG i) l
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  show Measurable fun a => (F a * G a) i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hFe i l).mul (hGe l j)

private lemma lintegral_inv_eq_of_mul_invariant {n : ℕ} (U : Set (Matrix (Fin n) (Fin n) ℂ)) (μR : Measure (Fin n → Fin n → ℂ))
    [SigmaFinite μR] (hne : μR ≠ 0)
    (hU : ∀ᵐ a ∂μR, Matrix.of a ∈ U) (hUu : ∀ a ∈ U, IsUnit a.det)
    (hleft : ∀ a ∈ U, ∀ h : (Fin n → Fin n → ℂ) → ENNReal, Measurable h →
        ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR = ∫⁻ b, h b ∂μR)
    (hright : ∀ a ∈ U, ∀ h : (Fin n → Fin n → ℂ) → ENNReal, Measurable h →
        ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR = ∫⁻ b, h b ∂μR)
    (u : (Fin n → Fin n → ℂ) → ENNReal) (hu : Measurable u) :
    ∫⁻ a, u (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR = ∫⁻ a, u a ∂μR := by
  have hm := measurable_mul_apply_of_measurable_entries (n := n)
  have hi := measurable_inv_apply_of_measurable_entries (n := n)
  have key : ∀ g : (Fin n → Fin n → ℂ) → ENNReal, Measurable g → ∀ h : (Fin n → Fin n → ℂ) → ENNReal,
      Measurable h → (∫⁻ b, g b ∂μR) * (∫⁻ a, h a ∂μR)
        = (∫⁻ b, h b ∂μR) * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR := by
    intro g hg h hh
    have hmb : ∀ b : Fin n → Fin n → ℂ,
        Measurable fun a : Fin n → Fin n → ℂ => g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) :=
      fun b => hg.comp (measurable_of_symm_mul (F := fun _ : Fin n → Fin n → ℂ => Matrix.of b)
        (G := fun a : Fin n → Fin n → ℂ => (Matrix.of a)⁻¹) measurable_const hi)
    have hmh : ∀ b : Fin n → Fin n → ℂ,
        Measurable fun a : Fin n → Fin n → ℂ => h (Matrix.of.symm (Matrix.of b * Matrix.of a)) :=
      fun b => hh.comp (measurable_of_symm_mul (F := fun _ : Fin n → Fin n → ℂ => Matrix.of b)
        (G := fun a : Fin n → Fin n → ℂ => Matrix.of a) measurable_const measurable_of_symm_of)
    calc (∫⁻ b, g b ∂μR) * (∫⁻ a, h a ∂μR)
        = ∫⁻ b, g b * ∫⁻ a, h a ∂μR ∂μR := (lintegral_mul_const _ hg).symm
      _ = ∫⁻ b, g b * ∫⁻ a, h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by
          refine lintegral_congr_ae (hU.mono fun b hb => ?_)
          dsimp only
          rw [hleft _ hb h hh]
      _ = ∫⁻ b, ∫⁻ a, g b * h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by
          refine lintegral_congr fun b => ?_
          exact (lintegral_const_mul _ (hmh b)).symm
      _ = ∫⁻ a, ∫⁻ b, g b * h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by
          refine lintegral_lintegral_swap ?_
          exact ((hg.comp measurable_fst).mul (hh.comp hm)).aemeasurable
      _ = ∫⁻ a, ∫⁻ b, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) * h b ∂μR ∂μR := by
          refine lintegral_congr_ae (hU.mono fun a ha => ?_)
          have hua := hUu _ ha
          have hψ : Measurable fun c : Fin n → Fin n → ℂ =>
              g (Matrix.of.symm (Matrix.of c * (Matrix.of a)⁻¹)) * h c :=
            (hg.comp (measurable_of_symm_mul (F := fun c : Fin n → Fin n → ℂ => Matrix.of c)
              (G := fun _ : Fin n → Fin n → ℂ => (Matrix.of a)⁻¹) measurable_of_symm_of measurable_const)).mul hh
          have := hright _ ha _ hψ
          have e : ∀ b : Fin n → Fin n → ℂ,
              Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of b * Matrix.of a)) * (Matrix.of a)⁻¹) = b := by
            intro b
            rw [Equiv.apply_symm_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hua]
            rfl
          simp only [e] at this
          exact this
      _ = ∫⁻ b, ∫⁻ a, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) * h b ∂μR ∂μR := by
          refine lintegral_lintegral_swap ?_
          exact ((hg.comp (measurable_of_symm_mul
            (F := fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.2)
            (G := fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => (Matrix.of q.1)⁻¹)
            measurable_snd (hi.comp measurable_fst))).mul (hh.comp measurable_snd)).aemeasurable
      _ = ∫⁻ b, h b * ∫⁻ a, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) ∂μR ∂μR := by
          refine lintegral_congr fun b => ?_
          rw [lintegral_mul_const _ (hmb b), mul_comm]
      _ = ∫⁻ b, h b * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR ∂μR := by
          refine lintegral_congr_ae (hU.mono fun b hb => ?_)
          have hub := hUu _ hb
          have := hright _ hb _ (hmb b)
          have e : ∀ a : Fin n → Fin n → ℂ,
              Matrix.of.symm (Matrix.of b * (Matrix.of (Matrix.of.symm (Matrix.of a * Matrix.of b)))⁻¹)
                = Matrix.of.symm (Matrix.of a)⁻¹ := by
            intro a
            rw [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hub]
          simp only [e] at this
          dsimp only
          rw [this]
      _ = (∫⁻ b, h b ∂μR) * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR := lintegral_mul_const _ hh
  obtain ⟨g0, hg0pos, hg0m, hg0lt⟩ := exists_pos_lintegral_lt_of_sigmaFinite μR (ε := 1) one_ne_zero
  have hg0m' : Measurable fun a => (g0 a : ENNReal) := hg0m.coe_nnreal_ennreal
  have htop : (∫⁻ a, (g0 a : ENNReal) ∂μR) ≠ ⊤ := (hg0lt.trans ENNReal.one_lt_top).ne
  have hz : (∫⁻ a, (g0 a : ENNReal) ∂μR) ≠ 0 := by
    intro h0
    rw [lintegral_eq_zero_iff hg0m'] at h0
    have hf : ∀ᵐ a ∂μR, False := h0.mono fun a ha => by
      simp only [Pi.zero_apply, ENNReal.coe_eq_zero] at ha
      exact (hg0pos a).ne' ha
    exact hne (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hf))
  have K := key u hu _ hg0m'
  rw [mul_comm] at K
  exact ((ENNReal.mul_right_inj hz htop).mp K).symm

theorem weil {k r : ℕ} (x : B.Mat k r) (hx : IsUnit x.det) (μR : Measure (Mt k r))
    (hR : B.IsHaarOn (C6.Rset x) μR) (μ : Measure (B.SS k r)) [SFinite μ]
    (hinvμ : ∀ a ∈ C6.Rset x, MeasurePreserving (C6.actR x a) μ μ)
    (Θ : B.SS k r → ENNReal) (hΘ : Measurable Θ)
    (h1 : ∀ᵐ p ∂μ, ∫⁻ a, Θ (C6.actR x (Matrix.of a) p) ∂μR = 1)
    (f : B.SS k r → ENNReal) (hf : Measurable f) :
    ∫⁻ p, f p ∂μ = ∫⁻ p, (∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR) ∂(μ.withDensity Θ) := by
  have hRs : ∀ a ∈ C6.Rset x, IsUnit a.det := fun a ha => WeylGroupFacts.isUnit_of_uh ha.1.1
  have : IsFiniteMeasureOnCompacts μR := ⟨fun K hK => hR.finite_compact K hK⟩
  have : SigmaFinite μR := inferInstance
  have hU : ∀ᵐ a ∂μR, Matrix.of a ∈ C6.Rset x := ae_iff.mpr (by exact hR.conc)
  have hact := measurable_actR_of x
  have hleft : ∀ a ∈ C6.Rset x, ∀ h : Mt k r → ENNReal, Measurable h →
      ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR = ∫⁻ b, h b ∂μR := by
    intro a ha h hh
    have hm : Measurable (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)) :=
      measurable_of_symm_mul (F := fun _ : Mt k r => a) (G := fun c : Mt k r => Matrix.of c) measurable_const measurable_id
    have e : μR.map (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)) = μR := hR.left a ha
    calc ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR
        = ∫⁻ b, h b ∂(μR.map (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r))) :=
          (lintegral_map hh hm).symm
      _ = ∫⁻ b, h b ∂μR := by rw [e]
  have hright : ∀ a ∈ C6.Rset x, ∀ h : Mt k r → ENNReal, Measurable h →
      ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR = ∫⁻ b, h b ∂μR := by
    intro a ha h hh
    have hm : Measurable (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r)) :=
      measurable_of_symm_mul (F := fun c : Mt k r => Matrix.of c) (G := fun _ : Mt k r => a) measurable_id measurable_const
    have e : μR.map (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r)) = μR := hR.right a ha
    calc ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR
        = ∫⁻ b, h b ∂(μR.map (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r))) :=
          (lintegral_map hh hm).symm
      _ = ∫⁻ b, h b ∂μR := by rw [e]
  have hF : Measurable fun p => ∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR :=
    (hf.comp (hact.comp measurable_swap)).lintegral_prod_right'
  have hfa : ∀ p : B.SS k r, Measurable fun a : Mt k r => f (C6.actR x (Matrix.of a) p) :=
    fun p => hf.comp (hact.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))
  have hΘa : ∀ p : B.SS k r, Measurable fun a : Mt k r => Θ (C6.actR x (Matrix.of a) p) :=
    fun p => hΘ.comp (hact.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))
  have hΘi : ∀ p : B.SS k r, Measurable fun a : Mt k r => Θ (C6.actR x (Matrix.of a)⁻¹ p) :=
    fun p => hΘ.comp (hact.comp (measurable_inv_apply_of_measurable_entries.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))
  rw [lintegral_withDensity_eq_lintegral_mul _ hΘ hF]
  symm
  calc ∫⁻ p, (Θ * fun p => ∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR) p ∂μ
      = ∫⁻ p, ∫⁻ a, Θ p * f (C6.actR x (Matrix.of a) p) ∂μR ∂μ := by
        refine lintegral_congr fun p => ?_
        rw [Pi.mul_apply, lintegral_const_mul _ (hfa p)]
    _ = ∫⁻ a, ∫⁻ p, Θ p * f (C6.actR x (Matrix.of a) p) ∂μ ∂μR := by
        refine lintegral_lintegral_swap ?_
        exact ((hΘ.comp measurable_fst).mul (hf.comp (hact.comp measurable_swap))).aemeasurable
    _ = ∫⁻ a, ∫⁻ p, Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p ∂μ ∂μR := by
        refine lintegral_congr_ae (hU.mono fun a ha => ?_)
        have hmp := hinvμ _ ha
        have hu := hRs _ ha
        have G : Measurable fun p => Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p :=
          (hΘ.comp (hact.comp ((measurable_const : Measurable fun _ : B.SS k r =>
            (Matrix.of.symm (Matrix.of a)⁻¹ : Mt k r)).prodMk measurable_id))).mul hf
        refine Eq.trans ?_ (hmp.lintegral_comp G)
        refine lintegral_congr fun p => ?_
        simp only [actR_inv_actR x hx _ hu]
    _ = ∫⁻ p, ∫⁻ a, Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p ∂μR ∂μ := by
        refine lintegral_lintegral_swap ?_
        exact ((hΘ.comp (hact.comp ((measurable_inv_apply_of_measurable_entries.comp measurable_fst).prodMk measurable_snd))).mul
          (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ p, f p * ∫⁻ a, Θ (C6.actR x (Matrix.of a)⁻¹ p) ∂μR ∂μ := by
        refine lintegral_congr fun p => ?_
        rw [lintegral_mul_const _ (hΘi p), mul_comm]
    _ = ∫⁻ p, f p * ∫⁻ a, Θ (C6.actR x (Matrix.of a) p) ∂μR ∂μ := by
        refine lintegral_congr fun p => ?_
        have := lintegral_inv_eq_of_mul_invariant (C6.Rset x) μR hR.ne_zero hU hRs hleft hright _ (hΘa p)
        exact congrArg (f p * ·) this
    _ = ∫⁻ p, f p ∂μ := lintegral_congr_ae (h1.mono fun p hp => by dsimp only; rw [hp, mul_one])

theorem isOrbQuot_withDensity : ∀ (k r : ℕ) (L : LocBessel k r) (x : B.Mat k r) (μR : Measure (Mt k r)) (θ : PairSp k r → ℝ) (cN : ℝ), IsRatioN k r cN → L.κN ≠ ⊤ → x ∈ B.GV k r → B.IsHaarOn (RStab k r x) μR → Measurable θ → (∀ p, 0 ≤ θ p) → (∀ p : PairSp k r, Matrix.of p.1.2 ∈ Nset k r → Matrix.of p.2.2 ∈ Nset k r → Matrix.of p.1.1 ∈ UWset k r L.z → Matrix.of p.2.1 ∈ UWset k r L.z' → ∫ a, θ (stabAct x (Matrix.of a) p) ∂μR = 1) → IsOrbQuot L x μR ((pairMeas L).withDensity fun p => ENNReal.ofReal (θ p)) := by
  intro k r L x μR θ cN hcN hκ hx hR hθ hθ0 h1
  have hxu : IsUnit x.det := WeylGroupFacts.isUnit_of_uh hx
  have hH : B.IsHaarOn (Nset k r) (Formalism.FourierDecayAlt.D.muN k r) := P.Dx2.MN.haar r
  have : IsFiniteMeasureOnCompacts (Formalism.FourierDecayAlt.D.muN k r) := ⟨fun K hK => hH.finite_compact K hK⟩
  have : SigmaFinite (Formalism.FourierDecayAlt.D.muN k r) := inferInstance
  have hμN : L.μN = (L.κN * ENNReal.ofReal cN) • Formalism.FourierDecayAlt.D.muN k r := by
    have e1 : Formalism.MainNotions.S.haarLie (Nset k r) L.κN = L.κN • Formalism.MainNotions.S.haarLie (Nset k r) 1 := by
      unfold Formalism.MainNotions.S.haarLie
      rw [one_smul]
    show Formalism.MainNotions.S.haarLie (Nset k r) L.κN = _
    rw [e1, hcN.2, smul_smul]
  have : SFinite L.μN := by rw [hμN]; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have : SFinite (pairMeas L) := by unfold pairMeas; infer_instance
  have hN : ∀ b ∈ Nset k r, MeasurePreserving (fun c : Mt k r => (Matrix.of.symm (b * Matrix.of c) : Mt k r))
      L.μN L.μN := by
    intro b hb
    have hc : Continuous (fun c : Mt k r => Matrix.of c) := continuous_id
    have hbc : Continuous (fun _ : Mt k r => b) := continuous_const
    refine ⟨(continuous_pi fun i => continuous_pi fun j => (hbc.matrix_mul hc).matrix_elem i j).measurable, ?_⟩
    rw [hμN, Measure.map_smul]
    congr 1
    exact hH.left b hb
  have hinv : ∀ a ∈ C6.Rset x, MeasurePreserving (C6.actR x a) (pairMeas L) (pairMeas L) := by
    intro a ha
    have e : C6.actR x a = Prod.map (Prod.map id (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)))
        (Prod.map id (fun c : Mt k r => (Matrix.of.symm (x⁻¹ * a * x * Matrix.of c) : Mt k r))) := rfl
    rw [e]
    exact ((MeasurePreserving.id L.μW).prod (hN a ha.1)).prod ((MeasurePreserving.id L.μW').prod (hN _ ha.2))
  have aW : ∀ᵐ h ∂L.μW, Matrix.of h ∈ UWset k r L.z := ae_iff.mpr L.hμW.1.2.2.1
  have aW' : ∀ᵐ h ∂L.μW', Matrix.of h ∈ UWset k r L.z' := ae_iff.mpr L.hμW'.1.2.2.1
  have aN : ∀ᵐ n ∂L.μN, Matrix.of n ∈ Nset k r := by
    refine ae_iff.mpr ?_
    rw [hμN, Measure.smul_apply, smul_eq_mul]
    exact mul_eq_zero_of_right _ hH.conc
  have aP : ∀ᵐ p ∂pairMeas L, (Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r) ∧
      (Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) := by
    show ∀ᵐ p ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)), _
    have q1 : ∀ᵐ z ∂(L.μW.prod L.μN), Matrix.of z.1 ∈ UWset k r L.z ∧ Matrix.of z.2 ∈ Nset k r :=
      (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
    have q2 : ∀ᵐ z ∂(L.μW'.prod L.μN), Matrix.of z.1 ∈ UWset k r L.z' ∧ Matrix.of z.2 ∈ Nset k r :=
      (Measure.quasiMeasurePreserving_fst.ae aW').and (Measure.quasiMeasurePreserving_snd.ae aN)
    exact (Measure.quasiMeasurePreserving_fst.ae q1).and (Measure.quasiMeasurePreserving_snd.ae q2)
  have h1' : ∀ᵐ p ∂pairMeas L, ∫⁻ a, ENNReal.ofReal (θ (C6.actR x (Matrix.of a) p)) ∂μR = 1 := by
    refine aP.mono fun p hp => ?_
    have hI := h1 p hp.1.2 hp.2.2 hp.1.1 hp.2.1
    have hint : Integrable (fun a : Mt k r => θ (stabAct x (Matrix.of a) p)) μR := by
      by_contra hni
      rw [integral_undef hni] at hI
      exact zero_ne_one hI
    have := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a => hθ0 _)
    rw [hI, ENNReal.ofReal_one] at this
    exact this.symm
  unfold IsOrbQuot
  intro f hf
  exact weil x hxu μR hR (pairMeas L) hinv (fun p => ENNReal.ofReal (θ p)) (ENNReal.measurable_ofReal.comp hθ)
    h1' f hf

end GlobalTheory.ThA.QuotCut
