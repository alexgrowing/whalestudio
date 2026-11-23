import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.SumEmbDualBasisComplex
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.FractionalIdealDualFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LiftMOneExt
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.MapMulLeftDenSpanImageEqMapNum

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem dual_eq_inv_mul_different (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
  rw [coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E), FractionalIdeal.dual_eq_mul_inv (𝓞 K) K I, mul_inv,
    inv_inv, mul_comm]

theorem coeIdeal_different_ne_zero (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E] :
    ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
  rw [coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E)]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero (𝓞 K) K one_ne_zero)

theorem lineR_eq (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (i : ι) :
    lineR M emb I i = imI M (emb i) (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) := by
  have h0 : liftM M 0 = 0 := by
    rw [liftM, dif_pos (zero_mem M)]
    rfl
  by_cases hI : I = 0
  · subst hI
    rw [zero_mul]
    have hm : mmR M emb (0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ⊥ := by
      rw [mmR, Submodule.span_eq_bot]
      rintro v ⟨a, ha, rfl⟩
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      funext k
      simp [h0]
    have hR : imI M (emb i) (0 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ⊥ := by
      rw [imI, Submodule.span_eq_bot]
      rintro y ⟨a, ha, rfl⟩
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      simp [h0]
    rw [hR, lineR, hm]
    ext x
    simp
  · have hJ : I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
      mul_ne_zero hI (coeIdeal_different_ne_zero K E)
    ext x
    rw [lineR, Submodule.mem_comap, mem_mmR_iff K E φ₀ M ι emb hinj hres hcard hM I hI,
      mem_imI_iff M (emb i) (hM i) _ hJ, ← dual_eq_inv_mul_different K E I]
    refine forall₂_congr fun b _ => ?_
    simp [Pi.single_apply]

theorem index_lineR (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (i : ι) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ lineR M emb I i) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M emb I i).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) : ℚ) : ℝ) ^
        Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by
  have hJ : I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    mul_ne_zero hI (coeIdeal_different_ne_zero K E)
  have heq := lineR_eq K E φ₀ M ι emb hinj hres hcard hM I i
  rw [heq] at hs ⊢
  exact index_imI M (emb i) (hM i) _ hJ s hs0 hs

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
