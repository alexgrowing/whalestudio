import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

noncomputable section

namespace GlobalTheory.PadicNormCastBounds

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_le_one_of_isIntegral {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hz : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  let v := NormedField.valuation (K := PadicAlgCl l)
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => by
      rw [Valuation.mem_integer_iff]
      exact_mod_cast hz a
  have h1 : IsIntegral v.integer x := hx.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl)
  have h2 := (Valuation.integer.integers v).mem_of_integral h1
  rw [Valuation.mem_integer_iff] at h2
  exact_mod_cast h2

theorem norm_natCast_of_coprime {a : ℕ} (ha : a.Coprime l) : ‖(a : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ha.symm

theorem norm_inv_pow_val_le (r e : ℕ) (u : (ZMod (l ^ r))ˣ) :
    ‖((((u : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (u : ZMod (l ^ 0)).val = 0 := by
      have := ZMod.val_lt (u : ZMod (l ^ 0))
      simpa using this
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · simp [he.ne']
  · have hc : (u : ZMod (l ^ r)).val.Coprime l :=
      (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_pow_self l hr.ne')
    rw [norm_inv, norm_pow, norm_natCast_of_coprime hc]
    simp

theorem norm_inv_pow_sub_le {a b r : ℕ} (e : ℕ) (ha : a.Coprime l) (hb : b.Coprime l) (h : a ≡ b [MOD l ^ r]) :
    ‖((a : PadicAlgCl l) ^ e)⁻¹ - ((b : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
  have na := norm_natCast_of_coprime ha
  have nb := norm_natCast_of_coprime hb
  have a0 : (a : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero))
  have b0 : (b : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero))
  obtain ⟨k, hk⟩ := (h.pow e).dvd
  have hk' : (b : PadicAlgCl l) ^ e - (a : PadicAlgCl l) ^ e = (l : PadicAlgCl l) ^ r * (k : PadicAlgCl l) := by
    exact_mod_cast congrArg (Int.cast : ℤ → PadicAlgCl l) hk
  rw [inv_sub_inv a0 b0, hk', norm_div, norm_mul, norm_mul, norm_pow (a : PadicAlgCl l), norm_pow (b : PadicAlgCl l),
    na, nb, one_pow, one_mul, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ k)

theorem twist_compat (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e : ℕ)
    (χ : (r : ℕ) → (ZMod (l ^ r))ˣ → Formalism.ConjugateSelfDual.Qbar l)
    (hO : ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), χ r x ∈ c.O)
    (hχ : ∀ (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r
      (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) : ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤
        ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => (((ZMod.val (x : ZMod (l ^ (r + 1))) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => (((ZMod.val (x : ZMod (l ^ r)) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ r x)
        (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
          ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤ ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖ := by
  have h1 := hχ r x
  generalize hy : Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
    ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x = y at h1 ⊢
  have hint : ‖χ r y‖ ≤ 1 :=
    norm_le_one_of_isIntegral
      ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨χ r y, hO r y⟩ : c.O)).map c.O.val)
  have hA := norm_inv_pow_val_le (r + 1) e x
  have hB := norm_inv_pow_val_le r e y
  have hAB : ‖((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹ -
      ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero (l : PadicAlgCl l), norm_one, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
      rwa [norm_neg]
    · refine norm_inv_pow_sub_le e
        ((ZMod.val_coe_unit_coprime x).coprime_dvd_right (dvd_pow_self l r.succ_ne_zero))
        ((ZMod.val_coe_unit_coprime y).coprime_dvd_right (dvd_pow_self l hr.ne')) ?_
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val, ← hy]
      rfl
  dsimp only
  set A := ((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  set B := ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  have hsplit : A * χ (r + 1) x - B * χ r y = A * (χ (r + 1) x - χ r y) + (A - B) * χ r y := by ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans h1
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hint).trans hAB

end GlobalTheory.PadicNormCastBounds

end
