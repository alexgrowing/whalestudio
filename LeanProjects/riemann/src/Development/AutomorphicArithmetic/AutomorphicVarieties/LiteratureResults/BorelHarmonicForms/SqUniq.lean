import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct
open Formalism.L2.Host GlobalTheory.UnitaryBC

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem chi_split {χ : HChar E} {s : ℝ} (h : χ.IsAbsPow s) :
    ((chiDet a χ (splitCentre E a 1) : ℂˣ) : ℂ) = ((Real.exp ((a : ℝ) * s * Fintype.card (E →+* ℂ)) : ℝ) : ℂ) := by
  have e : chiDet a χ (splitCentre E a 1) = chiInf χ (GeneralLinearGroup.det
      (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)))) :=
    congrArg χ.1 (det_infGL _)
  rw [e, GlobalTheory.CuspRep.InfType.chiInf_eq χ (fun σ => σ) (fun _ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun σ z hz =>
    ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz))) h.2.2]
  have d : ((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ))) : (Cinf E)ˣ) : Cinf E) =
      ((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a := by
    simp [Matrix.det_diagonal]
  have c : ∀ σ : E →+* ℂ, ‖coord σ (((expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ) : (Cinf E)ˣ) : Cinf E) ^ a)‖ =
      Real.exp a := fun σ => by
    have c1 : coord σ (fun _ : InfinitePlace E => ((1 : ℝ) : ℂ)) = 1 := map_one (coord σ)
    rw [map_pow, norm_pow, GlobalTheory.CuspRep.InfType.coord_expU, c1, Complex.norm_exp, Complex.one_re, Real.exp_one_pow]
  simp only [d, c]
  rw [← Complex.ofReal_cpow (Real.exp_pos _).le, ← Real.exp_mul, Finset.prod_const, Finset.card_univ,
    ← Complex.ofReal_pow, ← Real.exp_nat_mul, mul_comm]

omit [IsTotallyComplex E] in
private theorem absPow_uniq {χ χ' : HChar E} {s : ℝ} (h : χ.IsAbsPow s) (h' : χ'.IsAbsPow s) : χ = χ' := by
  rw [← mul_inv_eq_one]
  refine GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
  · rw [HChar.loc_mul, HChar.loc_inv, h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
  · have : χ.val v = χ'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
    rw [HChar.val_mul, HChar.val_inv, this, mul_inv_cancel]; simp
  · have : χ.inf k = χ'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
    rw [HChar.inf_mul, HChar.inf_inv, this, mul_inv_cancel]; simp

end

theorem UpperTheory.V.Lit.Bor.sqUniq :
    UpperTheory.V.Lit.Bor.SqUniq := by
  rintro E _ _ _ a ha r χ ⟨⟨s, hs⟩, htw⟩ φ hφ ⟨s', χ', hs', hsq⟩
  have hfun : ∀ ν : HChar E, (mulChi a ν φ).1 = fun g => ((chiDet a ν g : ℂˣ) : ℂ) * φ.1 g := fun ν =>
    funext fun g => by rw [mulChi_apply, mul_comm]
  by_cases h0 : ∀ g, φ.1 g = 0
  · rw [hfun]
    simpa only [h0, mul_zero] using hsq
  obtain ⟨g, hg⟩ := not_forall.1 h0
  have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
    rw [htw, hφ, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
  have h1 := aInv E a _ _ hz 1 g
  have h2 := hsq.1 1 g
  have h3 := aInv E a _ _ hφ 1 g
  simp only [hfun, zero_mul, Complex.exp_zero, one_mul, map_mul, Units.val_mul, h3] at h1 h2
  have key : ∀ x y : ℂ, y ≠ 0 → x * y * (Complex.exp (-(r : ℂ) * (1 : ℝ)) * φ.1 g) = y * φ.1 g →
      x = (Complex.exp (-(r : ℂ) * (1 : ℝ)))⁻¹ := fun x y hy h =>
    eq_inv_of_mul_eq_one_left (mul_right_cancel₀ (mul_ne_zero hy hg) (by linear_combination h))
  have h4 := (key _ _ (Units.ne_zero _) h1).trans (key _ _ (Units.ne_zero _) h2).symm
  rw [chi_split hs, chi_split hs', Complex.ofReal_inj, Real.exp_eq_exp] at h4
  have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain rfl : s = s' := mul_left_cancel₀ ha' (mul_right_cancel₀ hc h4)
  rw [hfun, absPow_uniq hs hs']
  exact hsq
