import Formalism.LocalToGlobal.UnitaryNorms.Lemmas

noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem mus_mono {M N : ℕ} (h : M ∣ N) : mus M ⊆ mus N := by
  intro z hz
  obtain ⟨c, rfl⟩ := h
  show z ^ (M * c) = 1
  rw [pow_mul, show z ^ M = 1 from hz, one_pow]

theorem cycQ_mono {M N : ℕ} (h : M ∣ N) : cycQ M ≤ cycQ N := adjoin.mono ℚ _ _ (mus_mono h)

theorem cycQplus_le (N : ℕ) : cycQplus N ≤ cycQ N := by
  rw [cycQplus, adjoin_le_iff]
  rintro _ ⟨z, hz, rfl⟩
  have : z ∈ cycQ N := subset_adjoin ℚ _ hz
  exact add_mem this (inv_mem this)

section Gauss

variable (q : ℕ) [Fact q.Prime]

def chiQb : MulChar (ZMod q) Qb := (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom Qb)

def psiQb {w : Qb} (hw : IsPrimitiveRoot w q) : AddChar (ZMod q) Qb := AddChar.zmodChar q hw.pow_eq_one

def gaussQb {w : Qb} (hw : IsPrimitiveRoot w q) : Qb := gaussSum (chiQb q) (psiQb q hw)

variable {q}

theorem gaussQb_mem {w : Qb} (hw : IsPrimitiveRoot w q) : gaussQb q hw ∈ cycQ q := by
  unfold gaussQb gaussSum
  refine sum_mem fun a _ => mul_mem ?_ ?_
  · show ((quadraticChar (ZMod q) a : ℤ) : Qb) ∈ _
    exact intCast_mem _ _
  · show AddChar.zmodChar q hw.pow_eq_one a ∈ _
    rw [AddChar.zmodChar_apply]
    exact pow_mem (subset_adjoin ℚ (mus q) (show w ∈ mus q from hw.pow_eq_one)) _

theorem gaussQb_sq (hq : q % 4 = 3) {w : Qb} (hw : IsPrimitiveRoot w q) :
    gaussQb q hw ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  have hq2 : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; rintro rfl; omega
  have hχ₁ : chiQb q ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hq2
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    show ((quadraticChar (ZMod q) a : ℤ) : Qb) ≠ 1
    rw [ha]; norm_num
  have hχ₂ : (chiQb q).IsQuadratic := MulChar.IsQuadratic.comp (quadraticChar_isQuadratic (ZMod q)) _
  have hψ : (psiQb q hw).IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root q hw
  have h := gaussSum_sq hχ₁ hχ₂ hψ
  unfold gaussQb
  rw [h, ZMod.card]
  show ((quadraticChar (ZMod q) (-1) : ℤ) : Qb) * _ = _
  rw [quadraticChar_neg_one hq2, ZMod.card, ZMod.χ₄_nat_three_mod_four hq]
  push_cast; ring

theorem sqQ_le_cycQ (hq : q % 4 = 3) : sqQ (-(q : ℤ)) ≤ cycQ q := by
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb q
  rw [sqQ_eq (gaussQb_sq hq hw), adjoin_simple_le_iff]
  exact gaussQb_mem hw

end Gauss

theorem EQ_le_cycQ (e : ℕ) {q d : ℕ} (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    EQ e q d ≤ cycQ (condN e q d) := by
  have := Fact.mk hq
  have := Fact.mk hd
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (sqQ_le_cycQ hq4).trans (cycQ_mono (q_dvd_condN e q d))
  · exact (sqQ_le_cycQ hd4).trans (cycQ_mono (d_dvd_condN e q d))
  · exact (cycQplus_le _).trans (cycQ_mono (two_pow_dvd_condN e q d))

end Formalism.L2.Host
