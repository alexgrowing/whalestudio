import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IterBochner

theorem ofReal_re_le (w : ℂ) : ENNReal.ofReal w.re ≤ ‖w‖ₑ :=
  (ENNReal.ofReal_le_ofReal (Complex.re_le_norm w)).trans (ofReal_norm_eq_enorm w).le

theorem ofReal_neg_re_le (w : ℂ) : ENNReal.ofReal (-w.re) ≤ ‖w‖ₑ :=
  (ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (Complex.abs_re_le_norm w))).trans (ofReal_norm_eq_enorm w).le

theorem ofReal_im_le (w : ℂ) : ENNReal.ofReal w.im ≤ ‖w‖ₑ :=
  (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Complex.abs_im_le_norm w))).trans (ofReal_norm_eq_enorm w).le

theorem ofReal_neg_im_le (w : ℂ) : ENNReal.ofReal (-w.im) ≤ ‖w‖ₑ :=
  (ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (Complex.abs_im_le_norm w))).trans (ofReal_norm_eq_enorm w).le

theorem integral_eq_four {Z : Type} [MeasurableSpace Z] (ν : Measure Z) (q : Z → ℂ) (hq : Measurable q)
    (hfin : ∫⁻ z, ‖q z‖ₑ ∂ν < ⊤) :
    ∫ z, q z ∂ν = (((∫⁻ z, ENNReal.ofReal (q z).re ∂ν).toReal - (∫⁻ z, ENNReal.ofReal (-(q z).re) ∂ν).toReal : ℝ) : ℂ) +
      (((∫⁻ z, ENNReal.ofReal (q z).im ∂ν).toReal - (∫⁻ z, ENNReal.ofReal (-(q z).im) ∂ν).toReal : ℝ) : ℂ) * Complex.I := by
  have hi : Integrable q ν := ⟨hq.aestronglyMeasurable, hfin⟩
  rw [← integral_re_add_im hi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi.re,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi.im]
  rfl

theorem integral_eq_four_of_ae {X : Type} [MeasurableSpace X] (μ : Measure X) (G : X → ℂ)
    (P₁ P₂ P₃ P₄ N : X → ENNReal) (h₁ : Measurable P₁) (h₂ : Measurable P₂) (h₃ : Measurable P₃) (h₄ : Measurable P₄)
    (l₁ : P₁ ≤ N) (l₂ : P₂ ≤ N) (l₃ : P₃ ≤ N) (l₄ : P₄ ≤ N) (hN : ∫⁻ x, N x ∂μ < ⊤)
    (hG : ∀ᵐ x ∂μ, G x = (((P₁ x).toReal - (P₂ x).toReal : ℝ) : ℂ) + (((P₃ x).toReal - (P₄ x).toReal : ℝ) : ℂ) * Complex.I) :
    ∫ x, G x ∂μ = (((∫⁻ x, P₁ x ∂μ).toReal - (∫⁻ x, P₂ x ∂μ).toReal : ℝ) : ℂ) +
      (((∫⁻ x, P₃ x ∂μ).toReal - (∫⁻ x, P₄ x ∂μ).toReal : ℝ) : ℂ) * Complex.I := by
  have fin : ∀ P : X → ENNReal, P ≤ N → ∫⁻ x, P x ∂μ ≠ ⊤ := fun P hP =>
    ((lintegral_mono fun x => hP x).trans_lt hN).ne
  have int : ∀ P : X → ENNReal, Measurable P → P ≤ N → Integrable (fun x => (P x).toReal) μ := fun P hm hP =>
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable (fin P hP)
  have itg : ∀ P : X → ENNReal, Measurable P → P ≤ N → ∫ x, (P x).toReal ∂μ = (∫⁻ x, P x ∂μ).toReal := fun P hm hP =>
    integral_toReal hm.aemeasurable (ae_lt_top hm (fin P hP))
  rw [integral_congr_ae hG]
  have i12 : Integrable (fun x => ((((P₁ x).toReal - (P₂ x).toReal : ℝ)) : ℂ)) μ :=
    ((int _ h₁ l₁).sub (int _ h₂ l₂)).ofReal (𝕜 := ℂ)
  have i34 : Integrable (fun x => ((((P₃ x).toReal - (P₄ x).toReal : ℝ)) : ℂ) * Complex.I) μ :=
    (((int _ h₃ l₃).sub (int _ h₄ l₄)).ofReal (𝕜 := ℂ)).mul_const Complex.I
  rw [integral_add i12 i34, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sub (int _ h₁ l₁) (int _ h₂ l₂), integral_sub (int _ h₃ l₃) (int _ h₄ l₄), itg _ h₁ l₁, itg _ h₂ l₂,
    itg _ h₃ l₃, itg _ h₄ l₄]

end GlobalTheory.IterBochner

namespace GlobalTheory.IterBochner

theorem measurable_lintegral2 {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μY : Measure Y) (μZ : Measure Z) [SFinite μY] [SFinite μZ] (g : X × Y × Z → ENNReal) (hg : Measurable g) :
    Measurable fun x => ∫⁻ y, ∫⁻ z, g (x, y, z) ∂μZ ∂μY := by
  have h1 : Measurable fun p : X × Y => ∫⁻ z, g (p.1, p.2, z) ∂μZ := by
    have : Measurable fun p : (X × Y) × Z => g (p.1.1, p.1.2, p.2) :=
      hg.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    exact this.lintegral_prod_right'
  exact h1.lintegral_prod_right'

theorem integral2_eq_four {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z] (μY : Measure Y) (μZ : Measure Z)
    [SFinite μZ] (q : Y → Z → ℂ) (hq : Measurable fun p : Y × Z => q p.1 p.2)
    (hfin : ∫⁻ y, ∫⁻ z, ‖q y z‖ₑ ∂μZ ∂μY < ⊤) :
    ∫ y, ∫ z, q y z ∂μZ ∂μY =
      (((∫⁻ y, ∫⁻ z, ENNReal.ofReal (q y z).re ∂μZ ∂μY).toReal - (∫⁻ y, ∫⁻ z, ENNReal.ofReal (-(q y z).re) ∂μZ ∂μY).toReal : ℝ) : ℂ) +
      (((∫⁻ y, ∫⁻ z, ENNReal.ofReal (q y z).im ∂μZ ∂μY).toReal - (∫⁻ y, ∫⁻ z, ENNReal.ofReal (-(q y z).im) ∂μZ ∂μY).toReal : ℝ) : ℂ) * Complex.I := by
  have hm : ∀ g : Y × Z → ENNReal, Measurable g → Measurable fun y => ∫⁻ z, g (y, z) ∂μZ := fun g hg =>
    hg.lintegral_prod_right'
  have hc : Measurable fun p : Y × Z => (q p.1 p.2).re := Complex.measurable_re.comp hq
  have hd : Measurable fun p : Y × Z => (q p.1 p.2).im := Complex.measurable_im.comp hq
  have hN : Measurable fun y => ∫⁻ z, ‖q y z‖ₑ ∂μZ := hm (fun p => ‖q p.1 p.2‖ₑ) hq.enorm
  refine integral_eq_four_of_ae μY (fun y => ∫ z, q y z ∂μZ) _ _ _ _ (fun y => ∫⁻ z, ‖q y z‖ₑ ∂μZ)
    (hm (fun p => ENNReal.ofReal (q p.1 p.2).re) (ENNReal.measurable_ofReal.comp hc))
    (hm (fun p => ENNReal.ofReal (-(q p.1 p.2).re)) (ENNReal.measurable_ofReal.comp hc.neg))
    (hm (fun p => ENNReal.ofReal (q p.1 p.2).im) (ENNReal.measurable_ofReal.comp hd))
    (hm (fun p => ENNReal.ofReal (-(q p.1 p.2).im)) (ENNReal.measurable_ofReal.comp hd.neg))
    (fun y => lintegral_mono fun z => ofReal_re_le _) (fun y => lintegral_mono fun z => ofReal_neg_re_le _)
    (fun y => lintegral_mono fun z => ofReal_im_le _) (fun y => lintegral_mono fun z => ofReal_neg_im_le _) hfin ?_
  filter_upwards [ae_lt_top hN hfin.ne] with y hy
  exact integral_eq_four μZ (q y) (hq.comp measurable_prodMk_left) hy

theorem integral3_eq_four {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (μX : Measure X)
    (μY : Measure Y) (μZ : Measure Z) [SFinite μY] [SFinite μZ] (q : X → Y → Z → ℂ)
    (hq : Measurable fun p : X × Y × Z => q p.1 p.2.1 p.2.2)
    (hfin : ∫⁻ x, ∫⁻ y, ∫⁻ z, ‖q x y z‖ₑ ∂μZ ∂μY ∂μX < ⊤) :
    ∫ x, ∫ y, ∫ z, q x y z ∂μZ ∂μY ∂μX =
      (((∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (q x y z).re ∂μZ ∂μY ∂μX).toReal -
        (∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (-(q x y z).re) ∂μZ ∂μY ∂μX).toReal : ℝ) : ℂ) +
      (((∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (q x y z).im ∂μZ ∂μY ∂μX).toReal -
        (∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (-(q x y z).im) ∂μZ ∂μY ∂μX).toReal : ℝ) : ℂ) * Complex.I := by
  have hm : ∀ g : X × Y × Z → ENNReal, Measurable g → Measurable fun x => ∫⁻ y, ∫⁻ z, g (x, y, z) ∂μZ ∂μY :=
    fun g hg => measurable_lintegral2 μY μZ g hg
  have hc : Measurable fun p : X × Y × Z => (q p.1 p.2.1 p.2.2).re := Complex.measurable_re.comp hq
  have hd : Measurable fun p : X × Y × Z => (q p.1 p.2.1 p.2.2).im := Complex.measurable_im.comp hq
  have hN : Measurable fun x => ∫⁻ y, ∫⁻ z, ‖q x y z‖ₑ ∂μZ ∂μY := hm (fun p => ‖q p.1 p.2.1 p.2.2‖ₑ) hq.enorm
  refine integral_eq_four_of_ae μX (fun x => ∫ y, ∫ z, q x y z ∂μZ ∂μY) _ _ _ _ (fun x => ∫⁻ y, ∫⁻ z, ‖q x y z‖ₑ ∂μZ ∂μY)
    (hm (fun p => ENNReal.ofReal (q p.1 p.2.1 p.2.2).re) (ENNReal.measurable_ofReal.comp hc))
    (hm (fun p => ENNReal.ofReal (-(q p.1 p.2.1 p.2.2).re)) (ENNReal.measurable_ofReal.comp hc.neg))
    (hm (fun p => ENNReal.ofReal (q p.1 p.2.1 p.2.2).im) (ENNReal.measurable_ofReal.comp hd))
    (hm (fun p => ENNReal.ofReal (-(q p.1 p.2.1 p.2.2).im)) (ENNReal.measurable_ofReal.comp hd.neg))
    (fun x => lintegral_mono fun y => lintegral_mono fun z => ofReal_re_le _)
    (fun x => lintegral_mono fun y => lintegral_mono fun z => ofReal_neg_re_le _)
    (fun x => lintegral_mono fun y => lintegral_mono fun z => ofReal_im_le _)
    (fun x => lintegral_mono fun y => lintegral_mono fun z => ofReal_neg_im_le _) hfin ?_
  filter_upwards [ae_lt_top hN hfin.ne] with x hx
  exact integral2_eq_four μY μZ (q x) (hq.comp measurable_prodMk_left) hx

end GlobalTheory.IterBochner

namespace GlobalTheory.IterBochner

theorem integral3_weight_eq_four {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (μX : Measure X)
    (μY : Measure Y) (μZ : Measure Z) [SFinite μY] [SFinite μZ] (φ : X → Y → Z → ℂ) (w : Y → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hφ : Measurable fun p : X × Y × Z => φ p.1 p.2.1 p.2.2) (hwm : Measurable w)
    (hfin : ∫⁻ x, ∫⁻ y, ∫⁻ z, ‖φ x y z‖ₑ * ENNReal.ofReal (w y) ∂μZ ∂μY ∂μX < ⊤) :
    ∫ x, ∫ y, ∫ z, φ x y z * ((w y : ℝ) : ℂ) ∂μZ ∂μY ∂μX =
      (((∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (φ x y z).re * ENNReal.ofReal (w y) ∂μZ ∂μY ∂μX).toReal -
        (∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (-(φ x y z).re) * ENNReal.ofReal (w y) ∂μZ ∂μY ∂μX).toReal : ℝ) : ℂ) +
      (((∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (φ x y z).im * ENNReal.ofReal (w y) ∂μZ ∂μY ∂μX).toReal -
        (∫⁻ x, ∫⁻ y, ∫⁻ z, ENNReal.ofReal (-(φ x y z).im) * ENNReal.ofReal (w y) ∂μZ ∂μY ∂μX).toReal : ℝ) : ℂ) *
        Complex.I := by
  have e0 : ∀ x y z, ‖φ x y z * ((w y : ℝ) : ℂ)‖ₑ = ‖φ x y z‖ₑ * ENNReal.ofReal (w y) := fun x y z => by
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((w y : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (hw y)]
  have e1 : ∀ x y z, ENNReal.ofReal (φ x y z * ((w y : ℝ) : ℂ)).re = ENNReal.ofReal (φ x y z).re * ENNReal.ofReal (w y) :=
    fun x y z => by rw [Complex.re_mul_ofReal, ENNReal.ofReal_mul' (hw y)]
  have e2 : ∀ x y z, ENNReal.ofReal (-(φ x y z * ((w y : ℝ) : ℂ)).re) =
      ENNReal.ofReal (-(φ x y z).re) * ENNReal.ofReal (w y) :=
    fun x y z => by rw [Complex.re_mul_ofReal, ← neg_mul, ENNReal.ofReal_mul' (hw y)]
  have e3 : ∀ x y z, ENNReal.ofReal (φ x y z * ((w y : ℝ) : ℂ)).im = ENNReal.ofReal (φ x y z).im * ENNReal.ofReal (w y) :=
    fun x y z => by rw [Complex.im_mul_ofReal, ENNReal.ofReal_mul' (hw y)]
  have e4 : ∀ x y z, ENNReal.ofReal (-(φ x y z * ((w y : ℝ) : ℂ)).im) =
      ENNReal.ofReal (-(φ x y z).im) * ENNReal.ofReal (w y) :=
    fun x y z => by rw [Complex.im_mul_ofReal, ← neg_mul, ENNReal.ofReal_mul' (hw y)]
  have hq : Measurable fun p : X × Y × Z => φ p.1 p.2.1 p.2.2 * ((w p.2.1 : ℝ) : ℂ) :=
    hφ.mul (Complex.measurable_ofReal.comp (hwm.comp measurable_snd.fst))
  have := integral3_eq_four μX μY μZ (fun x y z => φ x y z * ((w y : ℝ) : ℂ)) hq (by simpa only [e0] using hfin)
  simpa only [e1, e2, e3, e4] using this

end GlobalTheory.IterBochner

namespace GlobalTheory.IterBochner

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_inv_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a⁻¹ * mat a = 1 := by
  show (((a.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * (a.1 : Matrix (Fin n) (Fin n) (AE F E)) = 1
  exact Units.inv_mul _

theorem mat_mul_inv' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a : UA σ J) : mat a * mat a⁻¹ = 1 := by
  show (a.1 : Matrix (Fin n) (Fin n) (AE F E)) * (((a.1)⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
  exact Units.mul_inv _

theorem isLevi_inv {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} (H : Plane E n n₁) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J)
    (h : UA σ W.J) (hl : IsLevi H t h₁ h) : IsLevi H t⁻¹ h₁⁻¹ h⁻¹ := by
  obtain ⟨hx, hy, hι⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · have e : incV F H.x = mat h⁻¹ *ᵥ ((t : AE F E) • incV F H.x) := by
      rw [← hx, Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at e
    calc mat h⁻¹ *ᵥ incV F H.x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • ((t : AE F E) • mat h⁻¹ *ᵥ incV F H.x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [← e]
  · have e : incV F H.y = mat h⁻¹ *ᵥ (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y) := by
      rw [← hy, Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [Matrix.mulVec_smul] at e
    rw [inv_inv]
    calc mat h⁻¹ *ᵥ incV F H.y = cA σ (t : AE F E) • (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E) • mat h⁻¹ *ᵥ incV F H.y) := by
          rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
      _ = _ := by rw [← e]
  · calc mat h⁻¹ * incM F H.ι = mat h⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by
          rw [Matrix.mul_assoc (mat h⁻¹), Matrix.mul_assoc (incM F H.ι), mat_mul_inv', Matrix.mul_one]
      _ = mat h⁻¹ * (mat h * incM F H.ι) * mat h₁⁻¹ := by rw [hι]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]

theorem exists_decomp (B : Base F E) {n₁ : ℕ} (H : Plane E (n₁ + 2) n₁) (Y : Spc F E (n₁ + 2)) (Y₁ : Spc F E n₁) {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Submodule.span E (Y.L : Set (Fin (n₁ + 2) → E)) = ⊤) (v : Fin (n₁ + 2) → E) :
    ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hv : v ∈ Submodule.span E (Y.L : Set (Fin (n₁ + 2) → E)) := hL ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, u, rfl⟩ := ha
    obtain ⟨s', t', u', rfl⟩ := hb
    exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add, add_smul, add_smul]; abel⟩
  | smul c a _ ha =>
    obtain ⟨s, t, u, rfl⟩ := ha
    exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul, smul_add, smul_add, mul_smul, mul_smul]⟩

theorem incV_single {n : ℕ} (j : Fin n) : incV F (Pi.single j (1 : E)) = Pi.single j (1 : AE F E) := by
  funext i
  by_cases h : i = j
  · subst h; simp [incV]
  · simp [incV, Pi.single_apply, h]

theorem incV_decomp {n n₁ : ℕ} (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (s t : E) (u : Fin n₁ → E) :
    incV F (s • x + ι *ᵥ u + t • y) =
      inclR (F := F) (AF F) s • incV F x + incM F ι *ᵥ incV F u + inclR (F := F) (AF F) t • incV F y := by
  funext i
  simp only [incV, incM, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [RingHom.map_mulVec]
  rfl

end GlobalTheory.IterBochner

namespace GlobalTheory.IterBochner

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isTopologicalRing_AE : IsTopologicalRing (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

theorem continuous_cA' : Continuous (cA (F := F) (E := E) σ) := by
  haveI := isTopologicalRing_AE (F := F) (E := E)
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (cA (F := F) (E := E) σ).toLinearMap

variable (σ) in

def leviMat {n₁ : ℕ} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (H : Plane E (n₁ + 2) n₁) (s t : Fin (n₁ + 2) → E)
    (u : Fin (n₁ + 2) → Fin n₁ → E) (l : (AE F E)ˣ) (g : UA σ J₁) : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) (AE F E) :=
  Matrix.of fun i j => (inclR (F := F) (AF F) (s j) • ((l : AE F E) • incV F H.x) + (incM F H.ι * mat g) *ᵥ incV F (u j) +
    inclR (F := F) (AF F) (t j) • (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y)) i

theorem mat_eq_leviMat {n₁ : ℕ} {W : Spc F E (n₁ + 2)} {W₁ : Spc F E n₁} (H : Plane E (n₁ + 2) n₁) (s t : Fin (n₁ + 2) → E)
    (u : Fin (n₁ + 2) → Fin n₁ → E) (hdec : ∀ j, Pi.single j (1 : E) = s j • H.x + H.ι *ᵥ u j + t j • H.y)
    (l : (AE F E)ˣ) (g : UA σ W₁.J) (h : UA σ W.J) (hl : IsLevi H l g h) : mat h = leviMat σ H s t u l g := by
  ext i j
  have e := congrFun (congrArg (fun v => mat h *ᵥ v) (congrArg (incV F) (hdec j))) i
  rw [incV_single, Matrix.mulVec_single_one, incV_decomp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, hl.1, hl.2.1, hl.2.2] at e
  exact e

theorem continuous_leviMat {n₁ : ℕ} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (H : Plane E (n₁ + 2) n₁) (s t : Fin (n₁ + 2) → E)
    (u : Fin (n₁ + 2) → Fin n₁ → E) {X : Type} [TopologicalSpace X] (a : X → (AE F E)ˣ) (b : X → UA σ J₁)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun p : X => leviMat σ H s t u (a p) (b p) := by
  haveI := isTopologicalRing_AE (F := F) (E := E)
  have h1 : Continuous fun p : X => (a p : AE F E) := Units.continuous_val.comp ha
  have h2 : Continuous fun p : X => cA σ (((a p)⁻¹ : (AE F E)ˣ) : AE F E) :=
    continuous_cA'.comp (Units.continuous_coe_inv.comp ha)
  have h3 : Continuous fun p : X => mat (b p) :=
    Units.continuous_val.comp (continuous_subtype_val.comp hb)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hv : Continuous fun p : X =>
      inclR (F := F) (AF F) (s j) • ((a p : AE F E) • incV F H.x) + (incM F H.ι * mat (b p)) *ᵥ incV F (u j) +
        inclR (F := F) (AF F) (t j) • (cA σ (((a p)⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y) :=
by
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · exact (continuous_const : Continuous fun _ : X => inclR (F := F) (AF F) (s j)).smul
        (h1.smul (continuous_const : Continuous fun _ : X => incV F H.x))
    · exact ((continuous_const : Continuous fun _ : X => incM F H.ι).matrix_mul h3).matrix_mulVec
        (continuous_const : Continuous fun _ : X => incV F (u j))
    · exact (continuous_const : Continuous fun _ : X => inclR (F := F) (AF F) (t j)).smul
        (h2.smul (continuous_const : Continuous fun _ : X => incV F H.y))
  exact (continuous_apply i).comp hv

theorem continuous_of_isLevi {n₁ : ℕ} {W : Spc F E (n₁ + 2)} {W₁ : Spc F E n₁} (H : Plane E (n₁ + 2) n₁)
    (s t : Fin (n₁ + 2) → E) (u : Fin (n₁ + 2) → Fin n₁ → E)
    (hdec : ∀ j, Pi.single j (1 : E) = s j • H.x + H.ι *ᵥ u j + t j • H.y)
    (m : (AE F E)ˣ → UA σ W₁.J → UA σ W.J) (hm : ∀ l g, IsLevi H l g (m l g)) :
    Continuous fun p : (AE F E)ˣ × UA σ W₁.J => m p.1 p.2 := by
  haveI := (GlobalTheory.UnipCT.topFacts σ W₁.J).1
  have hM : Continuous fun p : (AE F E)ˣ × UA σ W₁.J => leviMat σ H s t u p.1 p.2 :=
    continuous_leviMat H s t u _ _ continuous_fst continuous_snd
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have e : ∀ p : (AE F E)ˣ × UA σ W₁.J, ((m p.1 p.2).1 : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) (AE F E)) =
        leviMat σ H s t u p.1 p.2 := fun p => mat_eq_leviMat H s t u hdec p.1 p.2 _ (hm p.1 p.2)
    exact (continuous_congr fun p => (e p).symm).1 hM
  · have e : ∀ p : (AE F E)ˣ × UA σ W₁.J,
        ((((m p.1 p.2).1)⁻¹ : GL (Fin (n₁ + 2)) (AE F E)) : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) (AE F E)) =
        leviMat σ H s t u p.1⁻¹ p.2⁻¹ := fun p =>
      mat_eq_leviMat H s t u hdec p.1⁻¹ p.2⁻¹ _ (isLevi_inv H _ _ _ (hm p.1 p.2))
    haveI := isTopologicalRing_AE (F := F) (E := E)
    have i1 : Continuous fun p : (AE F E)ˣ × UA σ W₁.J => p.1⁻¹ := continuous_inv.comp continuous_fst
    have i2 : Continuous fun p : (AE F E)ˣ × UA σ W₁.J => p.2⁻¹ := continuous_inv.comp continuous_snd
    have i3 : Continuous fun p : (AE F E)ˣ × UA σ W₁.J => leviMat σ H s t u p.1⁻¹ p.2⁻¹ :=
      continuous_leviMat H s t u _ _ i1 i2
    exact (continuous_congr fun p => (e p).symm).1 i3

end GlobalTheory.IterBochner

namespace GlobalTheory.IterBochner

theorem integral_levi_eq_four : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ f : UA σ G.V.J → ℂ, Continuous f →
      ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ‖f (m l g₀ * k.1)‖ₑ * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK < ⊤ →
      ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, f (m l g₀ * k.1) * (((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) ∂G₁.M.μ ∂μ ∂μK =
        (((∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal ((f (m l g₀ * k.1)).re) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal - (∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal (-(f (m l g₀ * k.1)).re) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal : ℝ) : ℂ) +
        (((∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal ((f (m l g₀ * k.1)).im) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal - (∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal (-(f (m l g₀ * k.1)).im) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal : ℝ) : ℂ) * Complex.I := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC _ hG hG₁ K μK μ _ _ hμ m hm f hf hfin
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI := isTopologicalRing_AE (F := F) (E := E)
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnipCT.topFacts σ G₁.V.J
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnipCT.topFacts σ G.V.J
  haveI : BorelSpace (UA σ G₁.V.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hG₁.hM.haar
  haveI hs0 : SigmaFinite μ := inferInstance
  haveI hs1 : SigmaFinite G₁.M.μ := inferInstance
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ hs0
  haveI : SFinite G₁.M.μ := @instSFiniteOfSigmaFinite _ _ _ hs1
  haveI : SFinite (G₁.M.μ.restrict G₁.M.dom) := inferInstance
  have hL : Submodule.span E (G.V.L : Set (Fin (b + 2) → E)) = ⊤ := hG.hV.lat.span_eq_top
  choose s t u hdec using fun j : Fin (b + 2) => exists_decomp B H G.V G₁.V hC.hH hL (Pi.single j 1)
  have hmc : Continuous fun p : (AE F E)ˣ × UA σ G₁.V.J => m p.1 p.2 := continuous_of_isLevi H s t u hdec m hm
  have hφ : Measurable fun p : K × (AE F E)ˣ × UA σ G₁.V.J => f (m p.2.1 p.2.2 * p.1.1) :=
    (hf.comp ((hmc.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst))).measurable
  have hwm : Measurable fun l : (AE F E)ˣ => (absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) :=
    (measurable_coe_nnreal_real.comp GlobalTheory.Doubling.continuous_absE.measurable).pow_const _
  exact integral3_weight_eq_four μK μ (G₁.M.μ.restrict G₁.M.dom) (fun k l g₀ => f (m l g₀ * k.1))
    (fun l => (absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) (fun l => Real.rpow_nonneg (NNReal.coe_nonneg _) _) hφ hwm hfin

end GlobalTheory.IterBochner
