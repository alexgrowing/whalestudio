import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemConePointsSpanX0
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.FiniteSupportLogCoeffGaussNorm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemMinimalPrimesOfMemFundCycleSupport
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PObjectsDivCycleGeneric
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivSuppHorizontalArithVar
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace RecQOfRecursion

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)

variable {n : ℕ}

theorem ne_zero_of_isChowFormCycle {F : Type*} [Field F] {Z : ProjCycle F n} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  exact mul_ne_zero (C_ne_zero.mpr hc)
    (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)

theorem exists_C_mul_of_isChowForm {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f g : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (hg : IsChowForm I k g) :
    ∃ r : F, r ≠ 0 ∧ g = C r * f := by
  obtain ⟨a, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨b, hb⟩ : f * a ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hf.1
    rw [mul_one, ← mul_assoc, ← hb]
  obtain ⟨r, hr, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
  exact ⟨r, hr.ne_zero, mul_comm _ _⟩

theorem map_genericIdeal (P : Ideal (MRing (PBlk n))) :
    (ObjectsChow.genericIdeal P).map (MvPolynomial.map (Rat.castHom ℂ)) = complexFibreIdeal P := by
  have h : (MvPolynomial.map (Rat.castHom ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) := by
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map]
    congr 1
  rw [ObjectsChow.genericIdeal, Ideal.map_map, h]
  rfl

theorem logFormNorm_eq (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℤ) :
    IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS (fun i => (u i : ℂ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.logNorm (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by
  funext z
  simp [IndefiniteRowSideFullHecke.ArithBezout.logFormNorm, ReciprocityTheory.ChartRestriction.G.Geo.logNorm, IndefiniteRowSideFullHecke.ArithBezout.linForm,
    ReciprocityTheory.ChartRestriction.G.Geo.Xc]

open Classical in

theorem divCycle_apply (P : Ideal (MRing (PBlk n))) (s : MRing (PBlk n)) (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W = if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0 :=
  rfl

def archData (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) :
    ArchData ℚ n where
  normAt _ := ObjectsHeight.ofPointMatrix S hS
  conj_norm _ u := by rw [ObjectsHeight.ofPointMatrix_norm, ObjectsHeight.ofPointMatrix_norm, hconj]

theorem integral_eq (hC : ComplexFibreCycle.Statement) (hI : ConeIntegralPts.Statement)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hsf : specFirst f (fun j => (u j : ℚ)) ≠ 0) :
    ∑ σ : ℚ →+* ℂ, cycleIntegral ((archData S hS hconj).normAt σ)
        (fundCycle ((ObjectsChow.genericIdeal P).map (MvPolynomial.map σ))) e
        (fsLog ((archData S hS hconj).normAt σ) fun j => σ (u j : ℚ)) =
      arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
        (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) := by
  have hu : (fun j => (Rat.castHom ℂ) (u j : ℚ)) = fun j => (u j : ℂ) := funext fun j => by simp
  rw [Fintype.sum_subsingleton _ (Rat.castHom ℂ), hu, map_genericIdeal]
  have hW : ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm (fun j => (u j : ℂ)) ∉ W := by
    refine ((hC n e δ P _ hP hf).2.2 _).mp ?_
    have h : IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℂ)) (map (Rat.castHom ℂ) f) =
        map (Rat.castHom ℂ) (specFirst f fun j => (u j : ℚ)) := by
      rw [ObjectsChow.specFirst_eq, ObjectsChow.map_specFirst, ← hu]
      rfl
    rw [h]
    exact fun h0 => hsf (map_injective _ (Rat.castHom ℂ).injective (by rw [h0, map_zero]))
  exact (hI n e S hS P _ hP hW).trans (by rw [logFormNorm_eq]; rfl)

theorem step (hRec : ChowHeightRecursionRat.Statement) (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
                              chowHt (archData S hS hconj) e δ (specFirst f fun j => (u j : ℚ)) +
                                (IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
                                  arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
                                    (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
      IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) e
        (specFirst f fun j => (u j : ℚ)) := by
  have hprime := VerticalPartGauss.isProjPrime_genericIdeal hP
  have hfA := VerticalPartGauss.isChowForm_genericIdeal hP hf
  have huA := VerticalPartGauss.linForm_not_mem_genericIdeal hP hu
  have hcyc := hSec ℚ n e (ObjectsChow.genericIdeal P) f _ hprime hfA huA
  have hcast : ∀ j, (((u j : ℤ) : 𝓞 ℚ) : ℚ) = (u j : ℚ) := fun j => by simp
  have key := hRec n e δ (archData S hS hconj) (ObjectsChow.genericIdeal P) f
    (fun j => ((u j : ℤ) : 𝓞 ℚ)) hprime hfA (ObjectsChow.isMultiHomog_of_isChowForm hf)
    (by simp only [hcast]; exact huA)
  simp only [hcast] at key
  refine ⟨?_, hcyc⟩
  rw [← ObjectsHeight.chowHt_eq_chowHeight (archData S hS hconj) S hS
      (fun _ u => ObjectsHeight.ofPointMatrix_norm S hS u), key, hV n e P u hP hu,
    integral_eq hC hI S hS hconj hP hf (ne_zero_of_isChowFormCycle hcyc), Module.finrank_self]
  simp

open Classical in

theorem horizontal (hMul : ChowHeightMul.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    {g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ} {d : Ideal (MRing (PBlk n)) → ℕ}
    (hP : IsArithVar P (e + 1 + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P)
    (hg : ∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W)))
    (hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ))) :
    chowHt (archData S hS hconj) (e + 1) δ (specFirst f fun j => (u j : ℚ)) =
      ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
        (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
          (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0) := by
  set s := IndefiniteRowSideFullHecke.ArithBezout.linForm u
  set Zh := (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).filter IsHorizontal with hZh
  have hmem : ∀ W ∈ Zh.support, W ∈ divSupp P s ∧ IsHorizontal W := by
    intro W hW
    rw [hZh, Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff, divCycle_apply] at hW
    exact ⟨by_contra fun h => hW.1 (if_neg h), hW.2⟩
  have hgA : ∀ W ∈ Zh.support, IsChowForm (ObjectsChow.genericIdeal W) (e + 1) (g W) := fun W hW =>
    VerticalPartGauss.isChowForm_genericIdeal
      (ObjectsChow.DivSuppHorizontalArithVar.proof n (e + 1) P u W hP hu (hmem W hW).1 (hmem W hW).2)
      (hg W (hmem W hW).1 (hmem W hW).2)
  have hsfne := ne_zero_of_isChowFormCycle hcyc
  obtain ⟨c, hc, g', hg', hsf⟩ := hcyc
  have hD := ObjectsChow.DivCycleGeneric.proof n (e + 1) P u hP hu
  rw [hD] at hsf hg'
  have hpos : ∀ W ∈ Zh.support,
      ObjectsChow.genericIdeal W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support := by
    intro W hW
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply]
    have h1 := Finset.single_le_sum (f := fun a => Finsupp.single (ObjectsChow.genericIdeal a) (Zh a)
      (ObjectsChow.genericIdeal W)) (fun _ _ => Nat.zero_le _) hW
    simp only [Finsupp.single_eq_same] at h1
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)) h1).ne'
  have hr : ∀ W ∈ Zh.support, ∃ r : ℚ, r ≠ 0 ∧ g' (ObjectsChow.genericIdeal W) = C r * g W :=
    fun W hW => exists_C_mul_of_isChowForm (hgA W hW) (hg' _ (hpos W hW))
  choose! r hr0 hr using hr
  have hsf' : specFirst f (fun j => (u j : ℚ)) =
      C (c * ∏ W ∈ Zh.support, r W ^ Zh W) * ∏ W ∈ Zh.support, g W ^ Zh W := by
    have hprod : ∏ W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support,
        g' W ^ (Zh.mapDomain ObjectsChow.genericIdeal) W =
          Zh.prod fun W m => g' (ObjectsChow.genericIdeal W) ^ m :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    rw [hsf, hprod, Finsupp.prod, Finset.prod_congr rfl (fun W hW =>
      show g' (ObjectsChow.genericIdeal W) ^ Zh W = C (r W ^ Zh W) * g W ^ Zh W by
        rw [hr W hW, mul_pow, map_pow]), Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]
  have hgne : ∀ W ∈ Zh.support, g W ≠ 0 := fun W hW => (hgA W hW).1
  have hgm : ∀ W ∈ Zh.support, IsMultiHomog (d W) (g W) := fun W hW =>
    ObjectsChow.isMultiHomog_of_isChowForm (hg W (hmem W hW).1 (hmem W hW).2)
  have hc' : c * ∏ W ∈ Zh.support, r W ^ Zh W ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hr0 W hW))
  have hδ : δ = ∑ W ∈ Zh.support, Zh W * d W := by
    have h1 : IsMultiHomog δ (specFirst f fun j => (u j : ℚ)) :=
      (ObjectsChow.isMultiHomog_of_isChowForm hf).specFirst _
    have h2 : IsMultiHomog (∑ W ∈ Zh.support, Zh W * d W) (specFirst f fun j => (u j : ℚ)) := by
      rw [hsf']
      unfold IsMultiHomog
      have := (isWeightedHomogeneous_C (groupWeight (e + 1) n) (c * ∏ W ∈ Zh.support, r W ^ Zh W)).mul
        (IsWeightedHomogeneous.prod Zh.support (fun W => g W ^ Zh W)
          (fun W => Zh W • fun _ : Fin (e + 1) => d W) fun W hW => (hgm W hW).pow (Zh W))
      convert this using 1
      funext i
      simp [Finset.sum_apply]
    exact congrFun (IsWeightedHomogeneous.inj_right hsfne h1 h2) 0
  rw [hsf', hδ, chowHt_C_mul_prod hMul _ Zh.support (⇑Zh) d g hgne hc']
  simp_rw [ObjectsHeight.chowHt_eq_chowHeight (archData S hS hconj) S hS
    (fun _ u => ObjectsHeight.ofPointMatrix_norm S hS u)]
  rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
  refine (Finset.sum_subset (fun W hW => (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mpr
    (hmem W hW).1) ?_).trans (Finset.sum_congr rfl fun W hW => ?_)
  · intro W _ hW
    rw [Finsupp.mem_support_iff, not_not] at hW
    rw [hW, Nat.cast_zero, zero_mul]
  · have hWd : W ∈ divSupp P s := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mp hW
    rw [hZh, Finsupp.filter_apply, divCycle_apply, if_pos hWd]
    split_ifs <;> simp

end RecQOfRecursion

open RecQOfRecursion in

theorem RecQOfRecursion.proof (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) : RecQOfRecursion.Statement := by
  intro hRec n S hS hconj
  refine ⟨fun δ P f u hP hf hu => ?_, fun e δ P f u g d hP hf hu hg => ?_⟩
  · obtain ⟨h, hcyc⟩ := step hRec hSec hV hC hI S hS hconj hP hf hu
    rw [h, chowHt_zero_groups_eq_zero _ _ (ne_zero_of_isChowFormCycle hcyc), zero_add]
  · obtain ⟨h, hcyc⟩ := step hRec hSec hV hC hI S hS hconj hP hf hu
    rw [h, horizontal (chowHeightMul_of_mahlerMul mahlerMul) S hS hconj hP hf hu hg hcyc,
      IndefiniteRowSideFullHecke.ArithBezout.vertPart, ← add_sub_assoc,
      ← finsum_mem_add_distrib (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite _ _)]
    congr 1
    refine finsum_mem_congr rfl fun W _ => ?_
    split_ifs <;> ring

end

end GroundTheory.Heights₂.Heights
