import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LRepTriangular

theorem firstCol_ne_zero (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ))
    (h0 : (((γ : M2) 0 0 : ℤ) : ZMod q) = 0) (h1 : (((γ : M2) 1 0 : ℤ) : ZMod q) = 0) : False := by
  have hd : (γ : M2).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hd
  have := congrArg (fun x : ℤ => (x : ZMod q)) hd
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h0, h1] at this
  simp at this

end GlobalTheory.EisM.LRepTriangular

namespace GlobalTheory.EisM

open GlobalTheory.EisM.LRepTriangular in

theorem lRep_DT_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repT q) := by
  intro L q hq hqL
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, x⟩ -
    have hγ := γ.2
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    refine ⟨?_, ?_⟩
    · show (((γ : SL(2, ℤ)) : M2) * repT q x).det = q
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]
      cases x <;> simp [repT, repU, Matrix.det_fin_two_of]
    · show (L : ℤ) ∣ (((γ : SL(2, ℤ)) : M2) * repT q x) 1 0
      cases x <;> simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | exact hγ | exact Dvd.dvd.mul_right hγ _
  · rintro ⟨γ, x⟩ - ⟨γ', y⟩ - h
    simp only at h
    have e : ∀ i k, (((γ : SL(2, ℤ)) : M2) * repT q x) i k = (((γ' : SL(2, ℤ)) : M2) * repT q y) i k :=
      fun i k => by rw [h]
    have hxy : x = y := by
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some j' =>
          exfalso
          have e00 := e 0 0; have e10 := e 1 0
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
          apply firstCol_ne_zero q (γ' : SL(2, ℤ))
          · rw [← e00]; push_cast; simp
          · rw [← e10]; push_cast; simp
      | some j =>
        cases y with
        | none =>
          exfalso
          have e00 := e 0 0; have e10 := e 1 0
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
          apply firstCol_ne_zero q (γ : SL(2, ℤ))
          · rw [e00]; push_cast; simp
          · rw [e10]; push_cast; simp
        | some j' =>
          have e00 := e 0 0; have e10 := e 1 0; have e01 := e 0 1; have e11 := e 1 1
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 e01 e11
          have c01 := congrArg (fun z : ℤ => (z : ZMod q)) e01
          have c11 := congrArg (fun z : ℤ => (z : ZMod q)) e11
          push_cast at c01 c11
          simp only [ZMod.natCast_self, mul_zero, add_zero, e00, e10] at c01 c11
          by_cases hJ : ((j : ℕ) : ZMod q) = ((j' : ℕ) : ZMod q)
          · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hJ
            rw [Fin.ext hJ]
          · exfalso
            have hs : ((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q) ≠ 0 := sub_ne_zero.mpr hJ
            apply firstCol_ne_zero q (γ' : SL(2, ℤ))
            · have : (((γ' : SL(2, ℤ)) : M2) 0 0 : ZMod q) * (((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q)) = 0 := by
                rw [mul_sub, c01, sub_self]
              exact (mul_eq_zero.mp this).resolve_right hs
            · have : (((γ' : SL(2, ℤ)) : M2) 1 0 : ZMod q) * (((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q)) = 0 := by
                rw [mul_sub, c11, sub_self]
              exact (mul_eq_zero.mp this).resolve_right hs
    subst hxy
    have hm : ((γ : SL(2, ℤ)) : M2) = ((γ' : SL(2, ℤ)) : M2) := by
      have h2 := congrArg (· * (repT q x).adjugate) h
      simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
      have hdet : (repT q x).det = q := by cases x <;> simp [repT, repU, Matrix.det_fin_two_of]
      rw [hdet] at h2
      exact smul_right_injective M2 hq0 h2
    exact Prod.ext (Subtype.ext (Subtype.ext hm)) rfl
  · rintro δ ⟨hdet, hL⟩
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, δ = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two δ⟩
    simp [Matrix.det_fin_two_of] at hdet hL
    by_cases hac : (q : ℤ) ∣ a ∧ (q : ℤ) ∣ c
    · obtain ⟨⟨a', ha⟩, ⟨c', hc⟩⟩ := hac
      subst ha hc
      have hdet' : a' * d - b * c' = 1 := by
        apply mul_left_cancel₀ hq0; linear_combination hdet
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL))
      have hLc : (L : ℤ) ∣ c' := hcop.dvd_of_dvd_mul_left hL
      let g : SL(2, ℤ) := ⟨!![a', b; c', d], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]; simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd c' L).mpr hLc
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k; fin_cases i <;> fin_cases k <;> simp [g, repT, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · have hd0 : (a : ZMod q) * d - b * c = 0 := by
        have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
        push_cast at this; simpa using this
      obtain ⟨J, hb, hd⟩ : ∃ J : ZMod q, (b : ZMod q) = (a : ZMod q) * J ∧ (d : ZMod q) = (c : ZMod q) * J := by
        by_cases ha : (a : ZMod q) = 0
        · have hc : (c : ZMod q) ≠ 0 := fun hc => hac
            ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc⟩
          refine ⟨d / c, ?_, ?_⟩
          · rw [ha, zero_mul]; rw [ha, zero_mul, zero_sub, neg_eq_zero] at hd0
            exact (mul_eq_zero.mp hd0).resolve_right hc
          · field_simp
        · refine ⟨b / a, ?_, ?_⟩
          · field_simp
          · field_simp; linear_combination hd0
      obtain ⟨u, hu⟩ : (q : ℤ) ∣ b - a * ((J.val : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val, hb]; ring
      obtain ⟨v, hv⟩ : (q : ℤ) ∣ d - c * ((J.val : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val, hd]; ring
      have hdet' : a * v - u * c = 1 := by
        apply mul_left_cancel₀ hq0; linear_combination hdet - a * hv + c * hu
      let g : SL(2, ℤ) := ⟨!![a, u; c, v], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]; simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd c L).mpr hL
      refine ⟨(⟨g, hg⟩, some ⟨J.val, ZMod.val_lt J⟩), trivial, ?_⟩
      ext i k; fin_cases i <;> fin_cases k <;> simp [g, repT, repU, Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val] <;> linarith

end GlobalTheory.EisM
