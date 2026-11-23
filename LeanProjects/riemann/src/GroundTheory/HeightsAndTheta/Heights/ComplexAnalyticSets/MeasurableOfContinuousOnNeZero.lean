import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

theorem fsPot_eq {n : ℕ} (h : HermNorm n) :
    fsPot h = fun y => 2 * Real.log (h.dualNorm y) := by
  funext y
  unfold fsPot
  rw [Real.log_pow]
  norm_num

theorem hessC_const_mul {D : ℕ} (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.hessC (fun w => c * φ w) z = (c : ℂ) • ReciprocityTheory.AnForm.hessC φ z := by
  have h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ := by
    have : (fun w => c * φ w) = c • φ := rfl
    rw [this, fderiv_const_smul_field]
  have h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ) := by
    rw [h1]
    exact fderiv_const_smul_field (f := fderiv ℝ φ) c
  ext i j
  simp only [ReciprocityTheory.AnForm.hessC, h2, Pi.smul_apply, Matrix.smul_apply,
    _root_.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem mdisc_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ReciprocityTheory.AnForm.mdisc (fun k => c • A k) = c ^ D * ReciprocityTheory.AnForm.mdisc A := by
  unfold ReciprocityTheory.AnForm.mdisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

theorem maDens_const_mul {D : ℕ} (c : ℝ) (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens (fun k w => c * φ k w) z = c ^ D * ReciprocityTheory.AnForm.maDens φ z := by
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hessC_const_mul, mdisc_smul]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem varInt_const_mul {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (g : (Fin n → ℂ) → ℝ)
    (c : ℝ) (ψ : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J e g (fun _ x => c * ψ x) =
      c ^ e * GroundTheory.Heights₂.Heights.varInt J e g (fun _ => ψ) := by
  unfold GroundTheory.Heights₂.Heights.varInt
  split_ifs with hA
  · unfold GroundTheory.Heights₂.Heights.chartInt GroundTheory.Heights₂.Heights.chartDens
      GroundTheory.Heights₂.Heights.sheetSum
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum]
    refine finsum_congr fun x => ?_
    classical
    rw [finsum_eq_if, finsum_eq_if]
    split_ifs with hx hs
    · have key : ReciprocityTheory.AnForm.maDens
          (fun k => (fun _ x => c * ψ x : Fin e → (Fin n → ℂ) → ℝ) k ∘ hs.choose) y =
          c ^ e * ReciprocityTheory.AnForm.maDens (fun k => (fun _ => ψ : Fin e → (Fin n → ℂ) → ℝ) k ∘
            hs.choose) y :=
        maDens_const_mul c (fun _ => ψ ∘ hs.choose) y
      dsimp only
      rw [key]
      ring
    · ring
    · ring
  · ring

theorem varInt_fsPot_eq_two_pow_mul {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (g : (Fin n → ℂ) → ℝ) :
    GroundTheory.Heights₂.Heights.varInt J e g (fun _ => fsPot h) =
      2 ^ e * GroundTheory.Heights₂.Heights.varInt J e g (fun _ x => Real.log (h.dualNorm x)) := by
  rw [fsPot_eq]
  exact varInt_const_mul J g 2 _

theorem le_ringKrullDim_slice {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) (hℓ : linForm ℓ ∉ J) :
    ((e : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) := by
  have hP := hJ.isPrime
  have hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J :=
      GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _)
        (htop ▸ Submodule.mem_top)
    exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpP : p.IsPrime := hp.1.1
  have hJp : J ≤ p := le_sup_left.trans hp.1.2
  have hht := Ideal.map_height_le_one_of_mem_minimalPrimes hp
  have hpm : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ
    (p.map (Ideal.Quotient.mk J))
  rw [hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at hform
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2)
      (Ideal.Quotient.factor_surjective hp.1.2)
  refine le_trans ?_ hle
  have key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b := by
    intro a b ha hab
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe k =>
        have h1 : k ≤ 1 := by exact_mod_cast ha
        have h2 : k + m = e + 1 := by exact_mod_cast hab
        exact_mod_cast (by omega : e ≤ m)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢
  induction D using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hform
    exact WithBot.bot_ne_coe hform
  | coe b =>
    have hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hform
    exact_mod_cast key _ b hht hab

theorem injective_projHom_of_finite_of_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J))
    (hfin : (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.Finite) :
    Function.Injective (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A) := by
  let f := (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom
  let P := RingHom.ker f
  let g : MvPolynomial (Fin d) ℂ ⧸ P →+* MvPolynomial (Fin n) ℂ ⧸ J := RingHom.kerLift f
  have hgf : g.comp (Ideal.Quotient.mk P) = f :=
    RingHom.ext fun a => RingHom.kerLift_mk f a
  have hg_fin : g.Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk P) (by rw [hgf]; exact hfin)
  let := g.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ ⧸ P) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hg_fin.to_isIntegral⟩
  have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap _ _)) fun _ _ hpq =>
      Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ ⧸ P) hpq
  have hd : ringKrullDim (MvPolynomial (Fin d) ℂ) = (d : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have haP : a ∈ P := ha
  have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero ha0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr haP)
  rw [hd] at h2
  have h3 := (add_le_add_left (hJ.trans h1) 1).trans h2
  have h4 : d + 1 ≤ d := by exact_mod_cast h3
  omega

theorem isFiniteProj_iff_of_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)) :
    IsFiniteProj J A ↔ GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A := by
  unfold IsFiniteProj
  rw [aeval_linForm_eq_projHom]
  exact ⟨fun h => ⟨injective_projHom_of_finite_of_le hJ h, h⟩, fun h => h.finite⟩

theorem varIntegral_eq_of_le {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (hJ : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)) :
    varIntegral J g φ = GroundTheory.Heights₂.Heights.varInt J d g φ := by
  have hp : (fun A : Matrix (Fin d) (Fin n) ℂ => IsFiniteProj J A) =
      fun A => GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A :=
    funext fun A => propext (isFiniteProj_iff_of_le hJ)
  unfold varIntegral GroundTheory.Heights₂.Heights.varInt
  by_cases h : ∃ A : Matrix (Fin d) (Fin n) ℂ,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A
  · have h' : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A := by
      obtain ⟨A, hA⟩ := h
      exact ⟨A, (isFiniteProj_iff_of_le hJ).mpr hA⟩
    rw [dif_pos h, dif_pos h', projInt_eq, choose_congr hp h' h]
  · have h' : ¬ ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProj J A := by
      rintro ⟨A, hA⟩
      exact h ⟨A, (isFiniteProj_iff_of_le hJ).mp hA⟩
    rw [dif_neg h, dif_neg h']

theorem slice_integral_eq {n e : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {ℓ : Fin n → ℂ} (g : (Fin n → ℂ) → ℝ) (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J)
    (hℓ : linForm ℓ ∉ J) :
    ((2 : ℝ) ^ e)⁻¹ * varIntegral (J ⊔ Ideal.span {linForm ℓ - 1}) g (fun _ : Fin e => fsPot h) =
      GroundTheory.Heights₂.Heights.varInt (J ⊔ Ideal.span {linForm ℓ - 1}) e g
        (fun _ x => Real.log (h.dualNorm x)) := by
  rw [varIntegral_eq_of_le _ _ _ (le_ringKrullDim_slice hJ hH hℓ), varInt_fsPot_eq_two_pow_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

theorem isProjPrime_of_isAffVariety {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) : IsProjPrime J := by
  refine ⟨hJ.isPrime, hH, ?_⟩
  by_contra hrel
  simp only [IsRelevant, not_exists, not_not] at hrel
  have hsurj : Function.Surjective (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨c, by rw [← Ideal.Quotient.mk_algebraMap]; rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p i _ =>
      exact ⟨0, by rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hrel i), mul_zero]⟩
  have h1 := ringKrullDim_le_of_surjective _ hsurj
  rw [hJ.dim, ringKrullDim_eq_zero_of_field] at h1
  have : e + 1 ≤ 0 := by exact_mod_cast h1
  omega

theorem exists_isChowForm_iff {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsProjPrime J) :
    (∃ F : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) F) ↔
      IsAffVariety J (e + 1) :=
  ⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩,
    fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J hJ hA.dim⟩

theorem measurable_of_continuousOn_ne_zero {n : ℕ} {g : (Fin n → ℂ) → ℝ}
    (hg : ContinuousOn g {x | x ≠ 0}) : Measurable g := by
  classical
  have hm : Measurable (Set.piecewise {x : Fin n → ℂ | x ≠ 0} g fun _ => g 0) :=
    hg.measurable_piecewise continuousOn_const (measurableSet_singleton _).compl
  convert hm using 1
  funext x
  by_cases hx : x = 0
  · subst hx
    simp [Set.piecewise]
  · simp [Set.piecewise, hx]

def ConeToProjectiveContinuous.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ), IsAffVariety J (e + 1) → IsHomogIdeal J → linForm ℓ ∉ J →
    ContinuousOn g {x | x ≠ 0} → (∀ c : ℂ, c ≠ 0 → ∀ y, g (c • y) = g y) →
      coneIntegral h J e g =
        ((2 : ℝ) ^ e)⁻¹ * varIntegral (J ⊔ Ideal.span {linForm ℓ - 1}) g (fun _ : Fin e => fsPot h)

theorem ConeToProjectiveContinuous.kleimanNef_field_of_alt (H : ConeToProjective.Statement) :
    ConeToProjectiveContinuous.Statement :=
  fun n e h J ℓ g hA hH hℓ hgc hg =>
    H n e h J ℓ g hA hH hℓ (measurable_of_continuousOn_ne_zero hgc) hg

theorem ConeToProjective.iff_continuous :
    GroundTheory.Heights₂.Heights.ConeToProjective.Statement ↔ ConeToProjectiveContinuous.Statement := by
  constructor
  · intro H n e h J ℓ g hA hH hℓ hgc hg
    have hP := isProjPrime_of_isAffVariety hA hH
    obtain ⟨F, hF⟩ := (exists_isChowForm_iff (e := e) hP).mpr hA
    rw [H n e h J F ℓ g hP hF hℓ (fun t x ht => hg t ht x) hgc, slice_integral_eq h g hA hH hℓ]
  · intro H n e h J F ℓ g hP hF hℓ hg hgc
    have hA : IsAffVariety J (e + 1) := (exists_isChowForm_iff hP).mp ⟨F, hF⟩
    rw [H n e h J ℓ g hA hP.isHomog hℓ hgc (fun c hc y => hg c y hc),
      slice_integral_eq h g hA hP.isHomog hℓ]

theorem ConeToProjective.kleimanNef_field_of_alt (H : ConeToProjective.Statement) :
    GroundTheory.Heights₂.Heights.ConeToProjective.Statement :=
  ConeToProjective.iff_continuous.mpr (ConeToProjectiveContinuous.kleimanNef_field_of_alt H)

theorem ConeToProjectiveContinuous.hypotheses_inhabited :
    IsAffVariety (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) (1 + 1) ∧
      IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      linForm (Pi.single (0 : Fin 2) (1 : ℂ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℂ)) ∧
      ContinuousOn (fun x : Fin 2 → ℂ => ‖x 0‖ ^ 2 / (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)) {x | x ≠ 0} ∧
      (∀ c : ℂ, c ≠ 0 → ∀ y : Fin 2 → ℂ,
        (fun x : Fin 2 → ℂ => ‖x 0‖ ^ 2 / (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)) (c • y) =
          (fun x : Fin 2 → ℂ => ‖x 0‖ ^ 2 / (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2)) y) := by
  obtain ⟨hA, hH, hℓ, -⟩ := ConeToProjective.hypotheses_inhabited
  have hpos : ∀ x : Fin 2 → ℂ, x ≠ 0 → ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 ≠ 0 := by
    intro x hx h0
    apply hx
    have h0' : ‖x 0‖ ^ 2 = 0 ∧ ‖x 1‖ ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp h0
    funext i
    fin_cases i
    · simpa using h0'.1
    · simpa using h0'.2
  refine ⟨hA, hH, hℓ, ?_, ?_⟩
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => hpos x hx
  · intro c hc y
    by_cases hy : y = 0
    · subst hy
      simp
    have hc2 : ‖c‖ ^ 2 ≠ 0 := by positivity
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [← mul_add, mul_div_mul_left _ _ hc2]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
