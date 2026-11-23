import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

open UpperHalfPlane MeasureTheory in
private theorem petHerm_cont (M k : ℕ) (f g : CuspForm (Gamma1 M) (k : ℤ)) (γ : SL(2, ℤ)) :
    Continuous fun z : ℍ => petersson (k : ℤ) f g (γ • z) :=
  (petersson_continuous _ (ModularFormClass.continuous f) (ModularFormClass.continuous g)).comp
    (continuous_const_smul (γ : GL (Fin 2) ℝ))

open UpperHalfPlane MeasureTheory in
private theorem petHerm_int (hF : UpperTheory.V.Af.Rs.FdFin) (M k : ℕ) [NeZero M] (f g : CuspForm (Gamma1 M) (k : ℤ)) (γ : SL(2, ℤ)) :
    IntegrableOn (fun z : ℍ => petersson (k : ℤ) f g (γ • z)) ModularGroup.fd := by
  obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f g
  exact Measure.integrableOn_of_bounded (M := B) hF.2.ne (petHerm_cont M k f g γ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => hB _)

open UpperHalfPlane in
private theorem petHerm_self (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    petersson (k : ℤ) f f z = ((Complex.normSq (f z) * z.im ^ k : ℝ) : ℂ) := by
  simp [petersson, Complex.normSq_eq_conj_mul_self]

open UpperHalfPlane MeasureTheory in
theorem UpperTheory.V.Lit.KT.petHerm :
    ∀ (M k : ℕ), 0 < M → (∀ f g h : CuspForm (Gamma1 M) (k : ℤ), pet M k f (g + h : CuspForm (Gamma1 M) (k : ℤ)) = pet M k f g + pet M k f h) ∧ (∀ (c : ℂ) (f g : CuspForm (Gamma1 M) (k : ℤ)), pet M k f (c • g : CuspForm (Gamma1 M) (k : ℤ)) = c * pet M k f g) ∧
    (∀ f g : CuspForm (Gamma1 M) (k : ℤ), pet M k g f = conj (pet M k f g)) ∧ ∀ f : CuspForm (Gamma1 M) (k : ℤ), pet M k f f = 0 → f = 0 := by
  intro M k hM
  haveI : NeZero M := ⟨hM.ne'⟩
  have hV : UpperTheory.V.Af.Rs.VolMap := UpperTheory.V.Af.Rs.volMap
  have hF : UpperTheory.V.Af.Rs.FdFin := UpperTheory.V.Af.Rs.fdFin (UpperTheory.V.Af.Rs.stripIm hV) hV
  have hP : UpperTheory.V.Af.Rs.FdPos := UpperTheory.V.Af.Rs.fdPos hV
  have : Finite (SL(2, ℤ) ⧸ Gamma1 M) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (SL(2, ℤ) ⧸ Gamma1 M) := Fintype.ofFinite _
  refine ⟨fun f g h => ?_, fun c f g => ?_, fun f g => ?_, fun f hf => ?_⟩
  · simp only [pet, finsum_eq_sum_of_fintype]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_add (petHerm_int hF M k f g _) (petHerm_int hF M k f h _)]
    congr 1
    funext z
    simp only [petersson, CuspForm.add_apply]
    ring
  · simp only [pet, finsum_eq_sum_of_fintype]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext z
    simp only [petersson, CuspForm.IsGLPos.smul_apply, smul_eq_mul]
    ring
  · simp only [pet, finsum_eq_sum_of_fintype]
    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← integral_conj]
    congr 1
    funext z
    exact petersson_symm _ _ _ _
  · by_contra hne
    obtain ⟨z0, hz0⟩ : ∃ z, f z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by ext z; simpa using hall z)
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z0
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gamma1 M) g
    have hre : (pet M k f f).re = ∑ γ : SL(2, ℤ) ⧸ Gamma1 M,
        ∫ z in ModularGroup.fd, (petersson (k : ℤ) f f (γ.out⁻¹ • z)).re := by
      simp only [pet, finsum_eq_sum_of_fintype]
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      exact (integral_re (petHerm_int hF M k f f _)).symm
    have h0 : ∀ z : ℍ, 0 ≤ (petersson (k : ℤ) f f z).re := fun z => by
      rw [petHerm_self, Complex.ofReal_re]
      exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le _)
    rw [hf, Complex.zero_re] at hre
    refine ne_of_lt (Finset.sum_pos' (fun γ _ => integral_nonneg fun z => h0 _)
      ⟨(g : SL(2, ℤ) ⧸ Gamma1 M), Finset.mem_univ _, ?_⟩) hre
    refine hP _ (Complex.continuous_re.comp (petHerm_cont M k f f _)) (fun z => h0 _)
      (petHerm_int hF M k f f _).re (g • z0) hg ?_
    rw [hh, mul_inv_rev, mul_smul, inv_smul_smul]
    have e : petersson (k : ℤ) f f (((h : SL(2, ℤ))⁻¹) • z0) = petersson (k : ℤ) f f z0 :=
      SlashInvariantFormClass.petersson_smul (Γ := (Gamma1 M : Subgroup (GL (Fin 2) ℝ)))
        (g := ((h⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨_, inv_mem h.2, rfl⟩
    rw [e, petHerm_self, Complex.ofReal_re]
    exact mul_pos (Complex.normSq_pos.2 hz0) (pow_pos z0.im_pos _)
