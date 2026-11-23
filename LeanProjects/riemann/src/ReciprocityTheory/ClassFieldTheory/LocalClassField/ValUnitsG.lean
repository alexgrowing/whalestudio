import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsF

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def redK : OK p K →+* resK p K :=
  (resMap p K).codRestrict (resK p K) fun x => (mem_resK_iff p K _).2 ⟨toObar p K x, (x : K).2, rfl⟩

theorem redK_eq_iff (a b : OK p K) :
    redK p K a = redK p K b ↔ ‖((a : K) : PadicAlgCl p) - ((b : K) : PadicAlgCl p)‖ < 1 := by
  rw [Subtype.ext_iff]
  show IsLocalRing.residue (Obar p) (toObar p K a) = IsLocalRing.residue (Obar p) (toObar p K b) ↔ _
  rw [residue_eq_iff]
  rfl

theorem redK_surjective : Function.Surjective (redK p K) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff p K c).1 hc
  exact ⟨⟨⟨x, hx⟩, x.2⟩, Subtype.ext rfl⟩

def UKtoOK : UK p K →* OK p K where
  toFun x := ⟨((x : Kˣ) : K), (mem_OK_iff p K _).2 (le_of_eq x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def redU : UK p K →* (resK p K)ˣ := MonoidHom.toHomUnits ((redK p K : OK p K →* resK p K).comp (UKtoOK p K))

variable {K}

def gradFun (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) (x : UKi p K i) : OK p K :=
  ⟨(((x : Kˣ) : K) - 1) / (π : K) ^ i, by
    rw [mem_OK_iff]
    show ‖((((x : Kˣ) : K) : PadicAlgCl p) - 1) / ((π : K) : PadicAlgCl p) ^ i‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one (pow_pos (norm_units_pos π) i), norm_pow_uniformiser p K hK hπ i]
    exact x.2.2⟩

theorem gradFun_val (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) (i : ℕ) (x : UKi p K i) :
    ((gradFun p hK hπ i x : K) : PadicAlgCl p) =
      ((((x : Kˣ) : K) : PadicAlgCl p) - 1) / ((π : K) : PadicAlgCl p) ^ i := rfl

def gradHom (hK : FiniteDimensional ℚ_[p] K) {π : Kˣ} (hπ : vK p K π = 1) {i : ℕ} (hi : 0 < i) :
    UKi p K i →* Multiplicative (resK p K) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (redK p K (gradFun p hK hπ i x))) fun x y => by
    rw [← ofAdd_add, ← map_add, Multiplicative.ofAdd.apply_eq_iff_eq, redK_eq_iff]
    have hP : ((π : K) : PadicAlgCl p) ^ i ≠ 0 := pow_ne_zero _ (coe_units_ne_zero π)
    have h1 : ((gradFun p hK hπ i (x * y) : K) : PadicAlgCl p) -
        (((gradFun p hK hπ i x + gradFun p hK hπ i y : OK p K) : K) : PadicAlgCl p) =
        ((gradFun p hK hπ i x : K) : PadicAlgCl p) * ((gradFun p hK hπ i y : K) : PadicAlgCl p) *
          ((π : K) : PadicAlgCl p) ^ i := by
      show ((gradFun p hK hπ i (x * y) : K) : PadicAlgCl p) -
        (((gradFun p hK hπ i x : K) : PadicAlgCl p) + ((gradFun p hK hπ i y : K) : PadicAlgCl p)) = _
      rw [gradFun_val, gradFun_val, gradFun_val]
      show (((((x : Kˣ) : K) : PadicAlgCl p) * (((y : Kˣ) : K) : PadicAlgCl p)) - 1) / _ - _ = _
      field_simp
      ring
    rw [h1, norm_mul, norm_mul, norm_pow, norm_pow_uniformiser p K hK hπ i]
    have h2 := (mem_OK_iff p K _).1 (gradFun p hK hπ i x).2
    have h3 := (mem_OK_iff p K _).1 (gradFun p hK hπ i y).2
    have h4 := rpow_neg_div_lt_one p K (eK_pos p K hK) hi
    have h5 := rpow_neg_div_nonneg p K i
    calc _ ≤ 1 * (p : ℝ) ^ (- (i : ℝ) / eK p K) :=
          mul_le_mul_of_nonneg_right (mul_le_one₀ h2 (norm_nonneg _) h3) h5
      _ < 1 := by rw [one_mul]; exact h4

variable (K)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
