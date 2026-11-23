import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HasTemperateGrowthArchPoly

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L3

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def xAd (x : UpperTheory.V.TR.Rinf F) : Ad F := ((UpperTheory.V.TR.infEq F x, 0) : InfiniteAdeleRing F × Af F)

theorem pInf_sInf (z : UpperTheory.V.TR.Rinf F) : UpperTheory.V.TR.pInf F (UpperTheory.V.TR.sInf F z) = z :=
  (UpperTheory.V.TR.infEq F).symm_apply_apply z

theorem pFin_sInf (z : UpperTheory.V.TR.Rinf F) : pFin F (UpperTheory.V.TR.sInf F z) = 0 := rfl

theorem pInf_sFin (z : Af F) : UpperTheory.V.TR.pInf F (sFin F z) = 0 := map_zero (UpperTheory.V.TR.infEq F).symm

theorem pFin_sFin (z : Af F) : pFin F (sFin F z) = z := rfl

theorem yAd_eq (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) :
    yAd y yf = (1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (y : UpperTheory.V.TR.Rinf F)) *
      (1 - sFin F 1 + sFin F (yf : Af F)) := rfl

theorem pInf_yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) :
    UpperTheory.V.TR.pInf F (yAd y yf) = (y : UpperTheory.V.TR.Rinf F) := by
  rw [yAd_eq]; simp [pInf_sInf, pInf_sFin]

theorem pFin_yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : pFin F (yAd y yf) = (yf : Af F) := by
  rw [yAd_eq]; simp [pFin_sInf, pFin_sFin]

theorem pInf_xAd (x : UpperTheory.V.TR.Rinf F) : UpperTheory.V.TR.pInf F (xAd x) = x :=
  (UpperTheory.V.TR.infEq F).symm_apply_apply x

theorem pFin_xAd (x : UpperTheory.V.TR.Rinf F) : pFin F (xAd x) = 0 := rfl

theorem gPt_val (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) :
    ((gPt x y yf : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) = !![yAd y yf, xAd x; 0, 1] := by
  have hI : Matrix.GeneralLinearGroup.map (UpperTheory.V.TR.pInf F) (gPt x y yf) = aff y x := by
    simp [gPt]
  have hF : Matrix.GeneralLinearGroup.map (pFin F) (gPt x y yf) = aff yf 0 := by
    simp [gPt]
  ext i j
  apply UpperTheory.V.TR.ad_ext
  · have e1 : UpperTheory.V.TR.pInf F ((gPt x y yf : Matrix (Fin 2) (Fin 2) (Ad F)) i j) =
        ((Matrix.GeneralLinearGroup.map (UpperTheory.V.TR.pInf F) (gPt x y yf) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
          Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j := rfl
    rw [e1, hI]
    fin_cases i <;> fin_cases j <;> simp [aff, pInf_yAd, pInf_xAd]
  · have e1 : pFin F ((gPt x y yf : Matrix (Fin 2) (Fin 2) (Ad F)) i j) =
        ((Matrix.GeneralLinearGroup.map (pFin F) (gPt x y yf) : GL (Fin 2) (Af F)) :
          Matrix (Fin 2) (Fin 2) (Af F)) i j := rfl
    rw [e1, hF]
    fin_cases i <;> fin_cases j <;> simp [aff, pFin_yAd, pFin_xAd]

theorem row_eq (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) (τ : IdeleGroup F) (ξ : Fin 2 → F) :
    rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      ![(τ : Ad F) * (algebraMap F (Ad F) (ξ 0) * yAd y yf),
        (τ : Ad F) * (algebraMap F (Ad F) (ξ 0) * xAd x + algebraMap F (Ad F) (ξ 1))] := by
  rw [Units.val_mul, gPt_val]
  funext i
  fin_cases i <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, rowA, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar] <;> ring

theorem translate_mem {f : Ad F → ℂ} (hf : f ∈ schwartzBruhat F) (d : Ad F) :
    (fun B => f (B + d)) ∈ schwartzBruhat F := by
  induction hf using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hg' : (fun z => g (z + d.2)) ∈ finiteSchwartzBruhat F :=
      ⟨hg.1.comp_continuous (continuous_add_const _), hg.2.comp_homeomorph (Homeomorph.addRight d.2)⟩
    convert schwartzBruhatTensor_mem (SchwartzMap.compSubConstCLM ℂ (-(homeomorphMixedSpace F d.1)) φ) hg' using 1
    funext B
    simp only [schwartzBruhatTensor, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    rw [homeomorphMixedSpace_apply, homeomorphMixedSpace_apply, homeomorphMixedSpace_apply]
    have hB : (B + d).1 = B.1 + d.1 := rfl
    rw [hB, (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_add]
    rfl
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul r G _ hG => exact Submodule.smul_mem _ r hG

theorem adelicFourier_translate (f : Ad F → ℂ) (d Z : Ad F) :
    adelicFourier F (fun B => f (B + d)) Z = (adelicChar F (-(d * Z)) : ℂ) * adelicFourier F f Z := by
  unfold adelicFourier
  have h := integral_add_right_eq_self (μ := adeleMeasure F)
    (fun B : Ad F => f B * (adelicChar F ((B - d) * Z) : ℂ)) d
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun B => ?_)
  simp only
  rw [sub_mul, sub_eq_add_neg, ← neg_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem ext_pInf (B : Ad F) (w : InfinitePlace F) :
    InfinitePlace.Completion.extensionEmbedding w (B.1 w) = ((UpperTheory.V.TR.pInf F B w : ℝ) : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  rfl

theorem char_xAd (ξ : F) (x : UpperTheory.V.TR.Rinf F) :
    (adelicChar F (-(algebraMap F (Ad F) ξ * xAd x)) : ℂ) = ex ξ x := by
  have h0 : -(algebraMap F (Ad F) ξ * xAd x) =
      ((-((algebraMap F (Ad F) ξ).1 * UpperTheory.V.TR.infEq F x), 0) : InfiniteAdeleRing F × Af F) := by
    refine Prod.ext rfl ?_
    show -((algebraMap F (Ad F) ξ).2 * 0) = 0
    simp
  have hT : infiniteTrace F ((algebraMap F (Ad F) ξ).1 * UpperTheory.V.TR.infEq F x) = ∑ v, reAt v ξ * x v := by
    show (∑ w : InfinitePlace F, (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w
      (((algebraMap F (Ad F) ξ).1 * UpperTheory.V.TR.infEq F x) w)).re) = _
    refine Finset.sum_congr rfl fun w _ => ?_
    have hm : (w.mult : ℝ) = 1 := by
      rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]; simp
    have h1 : InfinitePlace.Completion.extensionEmbedding w
        (((algebraMap F (Ad F) ξ).1 * UpperTheory.V.TR.infEq F x) w) = (w.embedding ξ) * ((x w : ℝ) : ℂ) := by
      show InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (Ad F) ξ).1 w * UpperTheory.V.TR.infEq F x w) = _
      rw [map_mul]
      congr 1
      · exact InfinitePlace.Completion.extensionEmbedding_coe w _
      · have := ext_pInf (xAd x) w
        rw [pInf_xAd] at this
        exact this
    rw [hm, h1, one_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, reAt]
  rw [h0, adelicChar_infinite, (infiniteTrace F).map_neg, neg_neg, Real.fourierChar_apply, ex, hT]
  congr 1
  push_cast
  ring

theorem tsum_split_zero (g : F → ℂ) (hg : Summable g) : ∑' ξ : F, g ξ = g 0 + ∑' ξ : Fˣ, g ξ := by
  rw [← hg.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton]
  congr 1
  let e : Fˣ ≃ ↥({0}ᶜ : Set F) :=
    { toFun := fun u => ⟨u, by simp [u.ne_zero]⟩
      invFun := fun z => Units.mk0 z.1 (Set.mem_compl_singleton_iff.mp z.2)
      left_inv := fun u => by ext; simp
      right_inv := fun z => by ext; simp }
  exact (e.tsum_eq (fun z => g z)).symm

theorem arch_le (a z : InfinitePlace F → ℝ) :
    ‖∏ v, (((a v : ℂ) + (z v : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a v : ℂ) ^ 2 + (z v : ℂ) ^ 2)))‖ ≤
      2 ^ Fintype.card (InfinitePlace F) *
        ‖∏ v, (((a v : ℂ) + Complex.I * (z v : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a v : ℂ) ^ 2 + (z v : ℂ) ^ 2)))‖ := by
  rw [norm_prod, norm_prod, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  rw [norm_mul, norm_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hre : ((a v : ℂ) + Complex.I * (z v : ℂ)).re = a v := by simp
  have him : ((a v : ℂ) + Complex.I * (z v : ℂ)).im = z v := by simp
  have h1 := Complex.abs_re_le_norm ((a v : ℂ) + Complex.I * (z v : ℂ))
  have h2 := Complex.abs_im_le_norm ((a v : ℂ) + Complex.I * (z v : ℂ))
  rw [hre] at h1
  rw [him] at h2
  calc ‖((a v : ℂ) + (z v : ℂ))‖ ≤ ‖(a v : ℂ)‖ + ‖(z v : ℂ)‖ := norm_add_le _ _
    _ = |a v| + |z v| := by rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 2 * ‖((a v : ℂ) + Complex.I * (z v : ℂ))‖ := by linarith

theorem fin_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z : Ad F) (P Q : Prop) [Decidable P] [Decidable Q]
    (hP : P ↔ (∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))) ∧
        (∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)))
    (hQ : Q ↔ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
        Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)) :
    ‖(if P then ((finiteAdelicChar F (pFin F Z) : Circle) : ℂ) else 0)‖ ≤
      ‖(if Q then ((finiteAdelicChar F (pFin F Z) : Circle) : ℂ) else 0)‖ := by
  by_cases h : P
  · have hq : Q := by
      rw [hQ]
      have h1 := hP.mp h
      refine fun w => ⟨le_trans (h1.1 w) ?_, h1.2 w⟩
      rw [WithZero.exp_le_exp]
      have : (0 : ℤ) ≤ dd w := by unfold dd; positivity
      omega
    rw [if_pos h, if_pos hq]
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

theorem kernF_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z : Ad F) :
    ‖kernF c A Z‖ ≤ 2 ^ Fintype.card (InfinitePlace F) * ‖PhiH c ![A, Z]‖ := by
  classical
  unfold kernF PhiH arch
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [norm_mul, norm_mul, ← mul_assoc]
  exact mul_le_mul (arch_le _ _) (fin_le c A Z _ _ Iff.rfl Iff.rfl) (norm_nonneg _) (by positivity)

theorem coe_mul_diag (τ : IdeleGroup F) (a : Fˣ) :
    ((τ * diagonal F a : IdeleGroup F) : Ad F) = (τ : Ad F) * algebraMap F (Ad F) (a : F) := by
  rw [Units.val_mul, coe_diagonal]

theorem module_mul_diag (τ : IdeleGroup F) (a : Fˣ) :
    ideleModule F (τ * diagonal F a) = ideleModule F τ := by
  rw [map_mul, ideleModule_diagonal, mul_one]

theorem inv_smul_diag (τ : IdeleGroup F) (a : Fˣ) (η : F) :
    (τ * diagonal F a)⁻¹ • algebraMap F (Ad F) ((a : F) * η) = τ⁻¹ • algebraMap F (Ad F) η := by
  have h : algebraMap F (Ad F) ((a⁻¹ : Fˣ) : F) * algebraMap F (Ad F) (a : F) = 1 := by
    rw [← (algebraMap F (Ad F)).map_mul, Units.inv_mul, map_one]
  rw [Units.smul_def, Units.smul_def, mul_inv_rev, Units.val_mul, ← map_inv, coe_diagonal,
    (algebraMap F (Ad F)).map_mul]
  linear_combination ((τ⁻¹ : IdeleGroup F) : Ad F) * algebraMap F (Ad F) η * h

theorem row_poisson {c : HeightOneSpectrum (𝓞 F) → ℕ} (hsl : ∀ A : Ad F, slice c A ∈ schwartzBruhat F)
    (Y X : Ad F) (τ : IdeleGroup F) (a : Fˣ) :
    ∑' b : F, Phi c ![(τ : Ad F) * (algebraMap F (Ad F) (a : F) * Y),
        (τ : Ad F) * (algebraMap F (Ad F) (a : F) * X + algebraMap F (Ad F) b)] =
      ∑' ξ : F, (adelicChar F (-(algebraMap F (Ad F) ξ * X)) : ℂ) * kern c Y (τ * diagonal F a) ξ := by
  have hRR := tsum_smul_algebraMap_eq τ
    (translate_mem (hsl ((τ : Ad F) * (algebraMap F (Ad F) (a : F) * Y))) ((τ : Ad F) * (algebraMap F (Ad F) (a : F) * X)))
  have hL : ∀ b : F, Phi c ![(τ : Ad F) * (algebraMap F (Ad F) (a : F) * Y),
      (τ : Ad F) * (algebraMap F (Ad F) (a : F) * X + algebraMap F (Ad F) b)] =
      slice c ((τ : Ad F) * (algebraMap F (Ad F) (a : F) * Y))
        (τ • algebraMap F (Ad F) b + (τ : Ad F) * (algebraMap F (Ad F) (a : F) * X)) := by
    intro b
    simp only [slice, Units.smul_def, smul_eq_mul]
    congr 3
    ring
  calc _ = _ := tsum_congr hL
    _ = _ := hRR
    _ = _ := by
      conv_rhs => rw [← (Equiv.mulLeft₀ (a : F) a.ne_zero).tsum_eq]
      rw [← tsum_mul_left]
      refine tsum_congr fun η => ?_
      have hm : (Equiv.mulLeft₀ (a : F) a.ne_zero) η = (a : F) * η := rfl
      rw [hm, adelicFourier_translate]
      unfold kern
      rw [inv_smul_diag, module_mul_diag, coe_mul_diag]
      have e1 : (τ : Ad F) * (algebraMap F (Ad F) (a : F) * X) * (τ⁻¹ • algebraMap F (Ad F) η) =
          algebraMap F (Ad F) ((a : F) * η) * X := by
        rw [Units.smul_def, (algebraMap F (Ad F)).map_mul]
        have : (τ : Ad F) * ((τ⁻¹ : IdeleGroup F) : Ad F) = 1 := Units.mul_inv τ
        linear_combination (algebraMap F (Ad F) (a : F) * X * algebraMap F (Ad F) η) * this
      have e2 : (τ : Ad F) * algebraMap F (Ad F) (a : F) * Y = (τ : Ad F) * (algebraMap F (Ad F) (a : F) * Y) := by
        ring
      rw [e1, e2]
      ring

def diagU (a b : IdeleGroup F) : GA F 2 where
  val := Matrix.diagonal ![(a : Ad F), (b : Ad F)]
  inv := Matrix.diagonal ![((a⁻¹ : IdeleGroup F) : Ad F), ((b⁻¹ : IdeleGroup F) : Ad F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; fin_cases i <;> simp

theorem summable_kern {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hP : SPois) (H : Hyp ω c) {κ : ℂ}
    (hκ : ∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z) (Y τ : IdeleGroup F) :
    Summable (fun p : Fˣ × F => ‖kern c (Y : Ad F) (τ * diagonal F p.1) p.2‖) := by
  obtain ⟨C, hC⟩ := hP F ω c H
  have hS := (hC (diagU (τ * Y) τ⁻¹)⁻¹).2.1
  rw [inv_inv] at hS
  let ι : Fˣ × F → {ξ : Fin 2 → F // ξ ≠ 0} := fun p =>
    ⟨![(p.1 : F), p.2], fun h => p.1.ne_zero (by simpa using congrFun h 0)⟩
  have hι : Function.Injective ι := by
    intro p q h
    have h0 := congrFun (congrArg Subtype.val h) 0
    have h1 := congrFun (congrArg Subtype.val h) 1
    simp only [ι, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    exact Prod.ext (Units.ext h0) h1
  have hS' := hS.comp_injective hι
  let e : Fˣ × F ≃ Fˣ × F :=
    { toFun := fun p => (p.1, (p.1 : F) * p.2)
      invFun := fun p => (p.1, (p.1 : F)⁻¹ * p.2)
      left_inv := fun p => Prod.ext rfl (inv_mul_cancel_left₀ p.1.ne_zero p.2)
      right_inv := fun p => Prod.ext rfl (mul_inv_cancel_left₀ p.1.ne_zero p.2) }
  rw [← e.summable_iff]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
    (hS'.mul_left (‖((ideleModule F τ : ℝ) : ℂ)⁻¹‖ * ‖κ‖ * 2 ^ Fintype.card (InfinitePlace F)))
  have hv : (((diagU (τ * Y) τ⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA (ι p).1) =
      ![(τ : Ad F) * algebraMap F (Ad F) (p.1 : F) * (Y : Ad F), τ⁻¹ • algebraMap F (Ad F) p.2] := by
    funext i
    fin_cases i <;> simp [diagU, ι, rowA, Matrix.mulVec_diagonal, Units.smul_def] <;> ring
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk]
  rw [hv]
  unfold kern
  rw [hκ, inv_smul_diag, module_mul_diag, coe_mul_diag, norm_mul, norm_mul]
  calc ‖((ideleModule F τ : ℝ) : ℂ)⁻¹‖ * (‖κ‖ * ‖kernF c ((τ : Ad F) * algebraMap F (Ad F) (p.1 : F) * (Y : Ad F))
        (τ⁻¹ • algebraMap F (Ad F) p.2)‖)
      ≤ ‖((ideleModule F τ : ℝ) : ℂ)⁻¹‖ * (‖κ‖ * (2 ^ Fintype.card (InfinitePlace F) *
          ‖PhiH c ![(τ : Ad F) * algebraMap F (Ad F) (p.1 : F) * (Y : Ad F), τ⁻¹ • algebraMap F (Ad F) p.2]‖)) := by
        gcongr
        exact kernF_le c _ _
    _ = _ := by ring

open Classical in

def rowEquiv : Fˣ ⊕ (Fˣ × F) ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun s := match s with
    | Sum.inl b => ⟨![0, (b : F)], fun h => b.ne_zero (by simpa using congrFun h 1)⟩
    | Sum.inr p => ⟨![(p.1 : F), p.2], fun h => p.1.ne_zero (by simpa using congrFun h 0)⟩
  invFun ξ := if h : ξ.1 0 = 0 then
      Sum.inl (Units.mk0 (ξ.1 1) (fun h1 => ξ.2 (by funext i; fin_cases i <;> simp [h, h1])))
    else Sum.inr (Units.mk0 (ξ.1 0) h, ξ.1 1)
  left_inv s := by
    rcases s with b | ⟨a, b⟩
    · simp
    · simp [a.ne_zero]
  right_inv ξ := by
    by_cases h : ξ.1 0 = 0
    · simp only [dif_pos h]
      ext i; fin_cases i <;> simp [h]
    · simp only [dif_neg h]
      ext i; fin_cases i <;> simp

theorem main_of (hsl : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
    {w | c w ≠ 0}.Finite → ∀ A : Ad F, slice c A ∈ schwartzBruhat F) : SPois → SFin → SKern → SPoint := by
  intro hP hFin hK F _ _ _ ω c H x y hy yf τ
  have hc := hFin F ω c H
  obtain ⟨κ, -, hκ⟩ := hK F c hc
  obtain ⟨C, hC⟩ := hP F ω c H
  have hsum := (hC (Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf)).1
  let f : (Fin 2 → F) → ℂ := fun ξ => Phi c ![(τ : Ad F) * (algebraMap F (Ad F) (ξ 0) * yAd y yf),
    (τ : Ad F) * (algebraMap F (Ad F) (ξ 0) * xAd x + algebraMap F (Ad F) (ξ 1))]
  have hrow : ∀ ξ : Fin 2 → F, Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) = f ξ := fun ξ => by rw [row_eq]
  have hth : thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf) =
      ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, f ξ.1 := tsum_congr fun ξ => hrow ξ.1
  have hfs : Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => f ξ.1) :=
    Summable.of_norm (by simpa only [hrow] using hsum)
  have hfe : Summable (fun s => f (rowEquiv s).1) :=
    (rowEquiv.summable_iff (f := fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => f ξ.1)).mpr hfs
  rw [hth, ← rowEquiv.tsum_eq (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => f ξ.1),
    Summable.tsum_sum (hfe.comp_injective Sum.inl_injective) (hfe.comp_injective Sum.inr_injective)]
  have h1 : ∑' b : Fˣ, f (rowEquiv (Sum.inl b)).1 = zeroRow c τ :=
    tsum_congr fun b => by simp [f, rowEquiv, zeroRow]
  have hprod : Summable (fun p : Fˣ × F => f (rowEquiv (Sum.inr p)).1) := hfe.comp_injective Sum.inr_injective
  have h2 : ∀ a : Fˣ, ∑' b : F, f (rowEquiv (Sum.inr (a, b))).1 =
      ∑' ξ : F, (adelicChar F (-(algebraMap F (Ad F) ξ * xAd x)) : ℂ) * kern c (yAd y yf) (τ * diagonal F a) ξ :=
    fun a => by rw [← row_poisson (hsl F c hc) (yAd y yf) (xAd x) τ a]; rfl
  have hK2 := summable_kern hP H hκ (UpperTheory.V.TR.infId F y * finId F yf) τ
  have hU : Summable (Function.uncurry fun (a : Fˣ) (ξ : F) =>
      (adelicChar F (-(algebraMap F (Ad F) ξ * xAd x)) : ℂ) * kern c (yAd y yf) (τ * diagonal F a) ξ) := by
    refine Summable.of_norm (hK2.congr fun p => ?_)
    simp only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul]
    rfl
  rw [h1, hprod.tsum_prod, tsum_congr h2, ← hU.tsum_comm]
  have hin : ∀ ξ : F, ∑' a : Fˣ, (adelicChar F (-(algebraMap F (Ad F) ξ * xAd x)) : ℂ) *
      kern c (yAd y yf) (τ * diagonal F a) ξ =
      (adelicChar F (-(algebraMap F (Ad F) ξ * xAd x)) : ℂ) * coefK c (yAd y yf) τ ξ := fun ξ => by
    rw [tsum_mul_left]; rfl
  have hsξ : Summable (fun ξ : F => (adelicChar F (-(algebraMap F (Ad F) ξ * xAd x)) : ℂ) * coefK c (yAd y yf) τ ξ) := by
    refine hU.prod_symm.prod.congr fun ξ => ?_
    exact hin ξ
  rw [tsum_congr hin, tsum_split_zero _ hsξ]
  simp only [map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, char_xAd]
  ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L3

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem sPoint_proof_of_slice (hsl : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (c : HeightOneSpectrum (𝓞 F) → ℕ), {w | c w ≠ 0}.Finite → ∀ A : Ad F, slice c A ∈ schwartzBruhat F) :
    SPois → SFin → SKern → SPoint := L3.main_of hsl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem pointwise_theta_expansion : SPois → SFin → SKern → SPoint :=
  sPoint_proof_of_slice (by intro F _ _ _ c hc A; exact slice_mem_sb hc A)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
