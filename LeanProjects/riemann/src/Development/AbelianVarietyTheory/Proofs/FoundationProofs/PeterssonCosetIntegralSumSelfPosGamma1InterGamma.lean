import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem petersson_self_eq (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    petersson k f f z = ((‖f z‖ ^ 2 * z.im ^ k : ℝ) : ℂ) := by
  rw [petersson, mul_comm (starRingEnd ℂ (f z)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

end GlobalTheory.Hk

namespace GlobalTheory.Hk

theorem pet_self_pos (N l : ℕ) (k : ℤ) (hN : 0 < N) (hl : 0 < l) (f : CuspForm (lev N l) k)
    (hf : f ≠ 0) :
    0 < (pet (lev N l) k ⇑f ⇑f).re ∧ (pet (lev N l) k ⇑f ⇑f).im = 0 := by
  haveI := lev_finiteIndex N l hN hl
  haveI : Finite (SL(2, ℤ) ⧸ lev N l) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (SL(2, ℤ) ⧸ lev N l) := Fintype.ofFinite _
  set r : ℍ → ℝ := fun z => ‖f z‖ ^ 2 * z.im ^ k with hr_def
  have hr0 : ∀ z, 0 ≤ r z := fun z => mul_nonneg (sq_nonneg _) (zpow_nonneg z.im_pos.le _)
  have hrc : Continuous r := by
    refine (f.holo'.continuous.norm.pow 2).mul ?_
    exact (continuous_im).zpow₀ k fun z => Or.inl z.im_ne_zero
  have hrp : ∀ z, petersson k f f z = (r z : ℂ) := fun z => petersson_self_eq k f z

  set I : SL(2, ℤ) ⧸ lev N l → ℝ := fun q => ∫ z in ModularGroup.fd, r (q.out⁻¹ • z) with hI
  have hpet : pet (lev N l) k ⇑f ⇑f = ((∑ q, I q : ℝ) : ℂ) := by
    rw [pet, finsum_eq_sum_of_fintype, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hrp, hI]
    exact integral_ofReal
  have hI0 : ∀ q, 0 ≤ I q := fun q => integral_nonneg fun z => hr0 _

  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (CuspForm.ext h)
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z₀
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (lev N l) g
  have hinv : ∀ z, r (((h⁻¹ : lev N l) : SL(2, ℤ)) • z) = r z := by
    intro z
    have e := SlashInvariantFormClass.norm_petersson_smul (f := f) (f' := f) (τ := z)
      (Γ := (lev N l : Subgroup (GL (Fin 2) ℝ)))
      (g := (((h⁻¹ : lev N l) : SL(2, ℤ)) : GL (Fin 2) ℝ)) ⟨_, (h⁻¹).2, rfl⟩
    rw [hrp, hrp, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hr0 _),
      Real.norm_of_nonneg (hr0 _)] at e
    exact e
  have hpt : (((g : SL(2, ℤ) ⧸ lev N l)).out⁻¹ • (g • z₀)) = ((h⁻¹ : lev N l) : SL(2, ℤ)) • z₀ := by
    rw [hh, smul_smul, mul_inv_rev, inv_mul_cancel_right]
    rfl
  have hIpos : 0 < I (g : SL(2, ℤ) ⧸ lev N l) := by
    have hpos : 0 < r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • (g • z₀)) := by
      rw [hpt, hinv]
      exact mul_pos (pow_pos (norm_pos_iff.2 hz₀) 2) (zpow_pos z₀.im_pos _)
    have hc : Continuous fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z) :=
      hrc.comp (continuous_const_smul (((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    have hint : IntegrableOn (fun z : ℍ => r ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)) ModularGroup.fd := by
      obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (lev N l : Subgroup (GL (Fin 2) ℝ)) f f
      have fin := UpperTheory.V.Af.Rs.fdFin (UpperTheory.V.Af.Rs.stripIm UpperTheory.V.Af.Rs.volMap) UpperTheory.V.Af.Rs.volMap
      refine Measure.integrableOn_of_bounded (M := C) fin.2.ne hc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      have := hC ((g : SL(2, ℤ) ⧸ lev N l).out⁻¹ • z)
      rw [hrp, Complex.norm_real] at this
      exact this
    exact UpperTheory.V.Af.Rs.fdPos UpperTheory.V.Af.Rs.volMap _ hc (fun z => hr0 _) hint _ hg hpos
  rw [hpet, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_pos' (fun q _ => hI0 q) ⟨_, Finset.mem_univ _, hIpos⟩, rfl⟩

end GlobalTheory.Hk
