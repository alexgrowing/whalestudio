import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTArith

noncomputable section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def bIdeal (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) : Ideal (𝓞 E) :=
  L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z) ⊓ differentIdeal ℤ (𝓞 E)

theorem relIndex_bIdeal (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0)
    (z : S.V) (hz : TrDual S L z) :
    (bIdeal S L z).toAddSubgroup.relIndex (differentIdeal ℤ (𝓞 E)).toAddSubgroup ≤ q ∧
    (bIdeal S L z).toAddSubgroup.relIndex (differentIdeal ℤ (𝓞 E)).toAddSubgroup ≠ 0 := by
  set g : 𝓞 E →+ S.V := (LinearMap.toSpanSingleton (𝓞 E) S.V z).toAddMonoidHom with hg
  have hc : (L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z)).toAddSubgroup = L.toAddSubgroup.comap g := by
    ext w; rfl
  have hb : (bIdeal S L z).toAddSubgroup =
      (L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z)).toAddSubgroup ⊓ (differentIdeal ℤ (𝓞 E)).toAddSubgroup := by
    ext w; rfl
  rw [hb, AddSubgroup.inf_relIndex_right, hc, AddSubgroup.relIndex_comap]
  have hle : (differentIdeal ℤ (𝓞 E)).toAddSubgroup.map g ≤ dualSub S L := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact diff_smul_mem S L z hz hδ
  have hq' : L.toAddSubgroup.relIndex (dualSub S L) ≠ 0 := by rw [hL.2]; exact hq
  refine ⟨hL.2 ▸ AddSubgroup.relIndex_le_of_le_right hle hq', fun h ↦ hq' ?_⟩
  exact AddSubgroup.relIndex_eq_zero_of_le_right hle h

theorem absNorm_bIdeal (S : HSpace E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0)
    (z : S.V) (hz : TrDual S L z) :
    Ideal.absNorm (bIdeal S L z) ≤ q * (discr E).natAbs ∧ Ideal.absNorm (bIdeal S L z) ≠ 0 := by
  obtain ⟨h1, h2⟩ := relIndex_bIdeal S q L hL hq z hz
  have hd : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hmul := AddSubgroup.relIndex_mul_index (H := (bIdeal S L z).toAddSubgroup)
    (K := (differentIdeal ℤ (𝓞 E)).toAddSubgroup) (fun x hx ↦ hx.2)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, hd] at hmul
  rw [← hmul]
  exact ⟨Nat.mul_le_mul_right _ h1, mul_ne_zero h2 hd0⟩

theorem one_le_norm (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (q : ℕ)
    (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0) (z : S.V) (hz : TrDual S L z)
    (ha : S.hT z z ≠ 0) :
    1 ≤ |Algebra.norm ℚ (S.hT z z)| * ((q : ℚ) * ((discr E).natAbs : ℚ) ^ 2) := by
  set a := S.hT z z with ha_def
  set 𝔟 := bIdeal S L z with h𝔟
  set 𝔡 := differentIdeal ℤ (𝓞 E) with h𝔡
  obtain ⟨hbn, hb0⟩ := absNorm_bIdeal S q L hL hq z hz
  have hd : Ideal.absNorm 𝔡 = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hle1 : spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) ≤ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨w, rfl⟩ := (mem_spanSingleton _).1 hi
    obtain ⟨b, hb, rfl⟩ := (mem_coeIdeal _).1 hj
    have hwb : w * b ∈ 𝔟 := 𝔟.mul_mem_left w hb
    have hL' : (w * b) • z ∈ L := hwb.1
    have hm := hT_right_mem_dual S hσ L z hz hL'
    have e : S.hT z ((w * b) • z) = w • a * algebraMap (𝓞 E) E b := by
      rw [← algebraMap_smul E (w * b) z, map_smul, smul_eq_mul, Algebra.smul_def, map_mul]
      ring
    rwa [e] at hm
  have hJ : spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔡 : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 :=
    (FractionalIdeal.mul_le.2 fun i hi j hj ↦ mul_mem_mul (hle1 hi) hj).trans dual_mul_diff.le
  have hJ0 : spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) * (𝔡 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · rwa [Ne, spanSingleton_eq_zero_iff]
    · rw [Ne, coeIdeal_eq_zero]
      intro h; apply hb0; change Ideal.absNorm 𝔟 = 0; rw [h, Ideal.absNorm_bot]
    · rw [Ne, coeIdeal_eq_zero]
      intro h; apply hd0; rw [← hd, h, Ideal.absNorm_bot]
  obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.1 hJ
  have hI0 : I ≠ ⊥ := by
    intro h; apply hJ0; rw [← hI, h, coeIdeal_bot]
  have hnI : (1 : ℚ) ≤ Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h ↦ hI0 (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hval : FractionalIdeal.absNorm (spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) *
      (𝔡 : FractionalIdeal (𝓞 E)⁰ E)) = |Algebra.norm ℚ a| * Ideal.absNorm 𝔟 * Ideal.absNorm 𝔡 := by
    rw [map_mul, map_mul, absNorm_span_singleton, coeIdeal_absNorm, coeIdeal_absNorm]
  rw [← hI, coeIdeal_absNorm] at hval
  rw [hval, hd] at hnI
  have hbq : (Ideal.absNorm 𝔟 : ℚ) ≤ q * (discr E).natAbs := by exact_mod_cast hbn
  have hN : 0 ≤ |Algebra.norm ℚ a| := abs_nonneg _
  have hD : (0 : ℚ) ≤ (discr E).natAbs := by positivity
  calc (1 : ℚ) ≤ |Algebra.norm ℚ a| * Ideal.absNorm 𝔟 * (discr E).natAbs := hnI
    _ ≤ |Algebra.norm ℚ a| * (q * (discr E).natAbs) * (discr E).natAbs := by gcongr
    _ = _ := by ring

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
