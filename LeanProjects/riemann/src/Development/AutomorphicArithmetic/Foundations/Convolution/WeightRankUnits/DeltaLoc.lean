import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolysStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOneStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem muAt_unit {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (u : Pl E) (k : Eˣ) :
    UpperTheory.ConvolutionTheory.G2.muAt μ u (k : E) = ((μ.locK u k : ℂˣ) : ℂ) := by
  have h : algebraMap E (u.adicCompletion E) (k : E) ≠ 0 := (_root_.map_ne_zero _).2 k.ne_zero
  unfold UpperTheory.ConvolutionTheory.G2.muAt
  rw [dif_pos h, show Units.mk0 _ h = atFin u k from Units.ext rfl]
  rfl

private theorem absHalf_sign {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) :
    absHalf w ((-1 : w.adicCompletion E) ^ n) = 1 := by
  obtain ⟨hm, hn⟩ := GlobalTheory.T.absHalf_mul_and_absHalf_neg_one E w
  have h1 : absHalf w (1 : w.adicCompletion E) = 1 := by
    have := hm (-1) (-1) (neg_ne_zero.2 one_ne_zero) (neg_ne_zero.2 one_ne_zero)
    rwa [neg_mul_neg, one_mul, hn, one_mul] at this
  rcases neg_one_pow_eq_or (w.adicCompletion E) n with h | h <;> rw [h]
  · exact h1
  · exact hn

theorem UpperTheory.ConvolutionTheory.G2.deltaLoc :
    UpperTheory.ConvolutionTheory.G2.DeltaLoc := by
  intro E _ _ _ _ μ e hμ a b P₁ P₂ h₁ h₂ hc w
  have hR : resultant P₁ P₂ ≠ 0 := Polynomial.resultant_ne_zero P₁ P₂ hc
  have hdeg₁ : (atPl w P₁).natDegree = a := by
    rw [atPl, Polynomial.natDegree_map]; exact h₁.2.1
  have hdeg₂ : (atPl w P₂).natDegree = b := by
    rw [atPl, Polynomial.natDegree_map]; exact h₂.2.1
  have hres : resultant (atPl w P₁) (atPl w P₂) = algebraMap E (w.adicCompletion E) (resultant P₁ P₂) := by
    rw [atPl, atPl, Polynomial.natDegree_map, Polynomial.natDegree_map]
    exact Polynomial.resultant_map_map P₁ P₂ _ _ _
  have hres' : resultant (atPl w P₁) (atPl w P₂) a b = algebraMap E (w.adicCompletion E) (resultant P₁ P₂) := by
    rw [← hres, hdeg₁, hdeg₂]
  have hconj := GlobalTheory.T.conj_resultant_of_ell_polys E a b P₁ P₂ h₁ h₂
  set R := resultant P₁ P₂ with hRdef
  set D : E := ((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a with hD
  have hDw : ((-1) ^ a * (atPl w P₁).coeff 0) ^ b * ((-1) ^ b * (atPl w P₂).coeff 0) ^ a =
      algebraMap E (w.adicCompletion E) D := by
    simp [atPl, Polynomial.coeff_map, hD]
  let k : Eˣ := Units.mk0 R hR
  have hk : (k : E) = R := rfl
  have hmu : ∀ u : Pl E, UpperTheory.ConvolutionTheory.G2.muAt μ u R = ((μ.locK u k : ℂˣ) : ℂ) := fun u => muAt_unit μ u k
  by_cases hsp : IsSplitAt w
  · have hsp' := hsp
    obtain ⟨u, hu, huw⟩ := hsp'
    have hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w, u} := by
      ext x
      refine ⟨fun hx => GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField E w u x hu huw hx, ?_⟩
      rintro (rfl | rfl)
      · rfl
      · exact huw
    rw [hfib, finprod_mem_pair (Ne.symm hu), hmu w, hmu u, GlobalTheory.T.absHalf_conjugatePlace_eq E w u hu huw R]
    let kc : Eˣ := Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k
    have hkc : (kc : E) = IsCMField.complexConj E R := rfl
    have hloc : μ.locK u k * μ.locK w kc = 1 := GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one E μ e hμ w u hu huw k
    have hs2 : ((-1 : E) ^ (a * b)) * (-1) ^ (a * b) = 1 := by
      rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
    have hsD : (-1) ^ (a * b) * D * (kc : E) = R := by
      rw [hkc]
      linear_combination (-1 : E) ^ (a * b) * hconj + R * hs2
    have hD0 : D ≠ 0 := by
      rintro h0
      rw [h0, mul_zero, zero_mul] at hsD
      exact hR hsD.symm
    have hwd : ((-1) ^ (a * b) * algebraMap E (w.adicCompletion E) D) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ((_root_.map_ne_zero _).2 hD0)
    have hunit : Units.mk0 _ hwd = atFin w (k * kc⁻¹) := by
      apply Units.ext
      have : (-1) ^ (a * b) * D = (k : E) * ((kc : E))⁻¹ := by
        rw [hk, ← hsD, mul_inv_cancel_right₀ kc.ne_zero]
      simp only [Units.val_mk0, atFin]
      rw [show (-1 : w.adicCompletion E) ^ (a * b) * algebraMap E (w.adicCompletion E) D =
        algebraMap E (w.adicCompletion E) ((-1) ^ (a * b) * D) by simp, this]
      simp
    have hfirst : ((μ.loc w (Units.mk0 _ hwd) : ℂˣ) : ℂ) = ((μ.locK w k : ℂˣ) : ℂ) * ((μ.locK u k : ℂˣ) : ℂ) := by
      rw [hunit]
      change ((μ.locK w (k * kc⁻¹) : ℂˣ) : ℂ) = _
      rw [map_mul, map_inv, eq_inv_of_mul_eq_one_right hloc, inv_inv, Units.val_mul]
    have hquot : R ^ 2 / D = (-1) ^ (a * b) * (R * IsCMField.complexConj E R) := by
      rw [div_eq_iff hD0]
      rw [hkc] at hsD
      linear_combination (-(-1 : E) ^ (a * b) * R) * hconj - R ^ 2 * hs2
    obtain ⟨hm, -⟩ := GlobalTheory.T.absHalf_mul_and_absHalf_neg_one E w
    have hA : ∀ x : E, x ≠ 0 → algebraMap E (w.adicCompletion E) x ≠ 0 := fun x hx => (_root_.map_ne_zero _).2 hx
    have hcR : IsCMField.complexConj E R ≠ 0 := (_root_.map_ne_zero _).2 hR
    have hsecond : absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) D) =
        absHalf w (algebraMap E (w.adicCompletion E) R) *
          absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E R)) := by
      rw [← map_pow, ← map_div₀, hquot, map_mul, map_mul, map_pow, map_neg, map_one,
        hm _ _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (mul_ne_zero (hA R hR) (hA _ hcR)),
        hm _ _ (hA R hR) (hA _ hcR), absHalf_sign, one_mul]
    unfold delta
    simp only [hdeg₁, hdeg₂, hDw, hres']
    rw [if_pos hsp, dif_pos hwd, hfirst, hsecond]
    ring
  · have hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w} := by
      ext x
      refine ⟨fun hx => ?_, ?_⟩
      · by_contra hxw
        exact hsp ⟨x, hxw, hx⟩
      · rintro rfl
        rfl
    rw [hfib, finprod_mem_singleton, hmu w, GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow E μ e hμ w hsp k]
    unfold delta
    simp only [hres]
    rw [if_neg hsp]
    rfl
