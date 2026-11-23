import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem norm_eq_rpow_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ = (p : ℝ) ^ (- (vK p K x : ℝ) / eK p K) := by
  have he' : (eK p K : ℝ) ≠ 0 := by positivity
  have h1 : - (vK p K x : ℝ) / eK p K = Real.logb p ‖((x : K) : PadicAlgCl p)‖ := by
    rw [vK_spec]; field_simp
  rw [h1, Real.rpow_logb (by linarith [one_lt_p_real p]) (one_lt_p_real p).ne' (norm_units_pos x)]

theorem norm_le_norm_iff_vK_of_pos (he : 0 < eK p K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x := by
  have he' : (0 : ℝ) < eK p K := by positivity
  rw [← Real.logb_le_logb (one_lt_p_real p) (norm_units_pos x) (norm_units_pos y), ← Int.cast_le (R := ℝ),
    vK_spec, vK_spec, neg_le_neg_iff, mul_le_mul_iff_right₀ he']

theorem norm_le_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he x 1
  rw [vK_one] at h
  simpa using h

theorem norm_lt_one_iff_vK_of_pos (he : 0 < eK p K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := by
  have h := norm_le_norm_iff_vK_of_pos p K he 1 x
  rw [vK_one] at h
  have h' : (1 : ℝ) ≤ ‖((x : K) : PadicAlgCl p)‖ ↔ vK p K x ≤ 0 := by simpa using h
  rw [← not_le, h']
  omega

theorem mem_UK_iff_of_pos (he : 0 < eK p K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1 ↔ _
  have h1 := norm_le_one_iff_vK_of_pos p K he x
  have h2 := norm_lt_one_iff_vK_of_pos p K he x
  constructor
  · intro h
    have h3 := h1.1 h.le
    have h4 : ¬ (1 ≤ vK p K x) := fun h5 => (h2.2 h5).ne h
    omega
  · intro h
    have h3 := h1.2 (by omega)
    have h4 : ¬ ‖((x : K) : PadicAlgCl p)‖ < 1 := fun h5 => by have := h2.1 h5; omega
    exact le_antisymm h3 (not_lt.1 h4)

theorem mem_UK_iff (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 :=
  mem_UK_iff_of_pos p K (eK_pos p K hK) x

theorem norm_eq_rpow_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ = (p : ℝ) ^ (- (vK p K x : ℝ) / eK p K) :=
  norm_eq_rpow_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ 1 ↔ 0 ≤ vK p K x := norm_le_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_lt_one_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ < 1 ↔ 1 ≤ vK p K x := norm_lt_one_iff_vK_of_pos p K (eK_pos p K hK) x

theorem norm_le_norm_iff_vK (hK : FiniteDimensional ℚ_[p] K) (x y : Kˣ) :
    ‖((x : K) : PadicAlgCl p)‖ ≤ ‖((y : K) : PadicAlgCl p)‖ ↔ vK p K y ≤ vK p K x :=
  norm_le_norm_iff_vK_of_pos p K (eK_pos p K hK) x y

theorem vK_p (x : Kˣ) (hx : ((x : K) : PadicAlgCl p) = (p : PadicAlgCl p)) : vK p K x = eK p K := by
  apply Int.cast_injective (α := ℝ)
  rw [vK_spec, hx, logb_norm_p]
  simp

def eLK : ℕ := eK p L / eK p K

def fLK : ℕ := fK p L / fK p K

variable {K L}

theorem multOf_mono (h : K ≤ L) : multOf p K ≤ multOf p L := fun _ hx => h hx

theorem valueGroup_mono (h : K ≤ L) : valueGroup p K ≤ valueGroup p L := AddSubgroup.map_mono (multOf_mono p h)

theorem eK_dvd_of_le (h : K ≤ L) : eK p K ∣ eK p L :=
  ⟨_, (AddSubgroup.relIndex_mul_relIndex (AddSubgroup.zmultiples (1 : ℝ)) (valueGroup p K) (valueGroup p L)
    (AddSubgroup.zmultiples_le_of_mem (one_mem_valueGroup p K)) (valueGroup_mono p h)).symm⟩

theorem eK_eq_mul_of_le (h : K ≤ L) : eK p L = eLK p K L * eK p K := (Nat.div_mul_cancel (eK_dvd_of_le p h)).symm

theorem eK_eq_mul (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : eK p L = eLK p K L * eK p K := eK_eq_mul_of_le p h

theorem eK_eq_of_norm (h : K ≤ L) (hn : ∀ x ∈ L, ∃ y ∈ K, ‖x‖ = ‖y‖) : eK p L = eK p K := by
  have h1 : valueGroup p L = valueGroup p K := by
    refine le_antisymm ?_ (valueGroup_mono p h)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hn _ hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [norm_zero, norm_eq_zero] at hxy
      exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero hxy
    refine ⟨Additive.ofMul (Units.mk0 y hy0), hy, ?_⟩
    rw [vbar_apply p x, hxy]
    rfl
  unfold eK
  rw [h1]

theorem eK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eK p (Kn p K n) = eK p K :=
  eK_eq_of_norm p (le_Kn p K n) fun _ hx => norm_Kn p K hK hn hx

theorem eLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : eLK p K (Kn p K n) = 1 := by
  rw [eLK, eK_Kn p hK hn, Nat.div_self (eK_pos p K hK)]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
