import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped Classical nonZeroDivisors

namespace GlobalTheory.DivCls

theorem classes_finite (E : Type) [Field E] [NumberField E] : ∃ T : Finset (HeightOneSpectrum (𝓞 E) → ℤ),
      ∀ g : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support g).Finite →
        ∃ r ∈ T, ∃ a : E, a ≠ 0 ∧ ∀ P, g P = r P + ord P a := by
  have hrep : ∀ c : ClassGroup (𝓞 E), ∃ J : (FractionalIdeal (𝓞 E)⁰ E)ˣ, ClassGroup.mk E J = c :=
    fun c => ClassGroup.induction (P := fun c => ∃ J : (FractionalIdeal (𝓞 E)⁰ E)ˣ, ClassGroup.mk E J = c) E
      (fun I => ⟨I, rfl⟩) c
  choose J hJ using hrep
  refine ⟨Finset.univ.image (fun c => fun P => FractionalIdeal.count E P ((J c : FractionalIdeal (𝓞 E)⁰ E))), ?_⟩
  intro g hg
  set exps := Finsupp.ofSupportFinite g hg
  set I : FractionalIdeal (𝓞 E)⁰ E := exps.prod (fun v n => (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ n) with hIdef
  have hI : I ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun v _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))
  have hcI : ∀ P, FractionalIdeal.count E P I = g P := by
    intro P
    rw [hIdef, FractionalIdeal.count_finsuppProd]
    rfl
  set c := ClassGroup.mk E (Units.mk0 I hI)
  have hmk : ClassGroup.mk E ((Units.mk0 I hI) * (J c)⁻¹) = 1 := by
    rw [map_mul, map_inv, hJ c, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at hmk
  obtain ⟨x, hx⟩ := hmk
  have hJ0 : ((J c : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := (J c).ne_zero
  have hK0 : ((((Units.mk0 I hI) * (J c)⁻¹ : (FractionalIdeal (𝓞 E)⁰ E)ˣ)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := Units.ne_zero _
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [FractionalIdeal.spanSingleton_zero] at hx; exact hK0 hx
  refine ⟨_, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, x, hx0, fun P => ?_⟩
  have e := congrArg (FractionalIdeal.count E P) hx
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
    FractionalIdeal.count_mul E P hI (inv_ne_zero hJ0), FractionalIdeal.count_inv, hcI] at e
  simp only [ord]
  omega

end GlobalTheory.DivCls
