import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

noncomputable section

namespace GlobalTheory.HWL.Coord

variable {l : ℕ} [hl : Fact l.Prime]

def large₂ (u : ℤ_[l]ˣ) : ℚ_[l] := Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l])

theorem norm_coe_unit (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u

theorem Lg_mul (u w : ℤ_[l]ˣ) : large₂ (u * w) = large₂ u + large₂ w := by
  rw [large₂, Units.val_mul, PadicInt.coe_mul]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_coe_unit u) (norm_coe_unit w)

theorem Lg_one : large₂ (1 : ℤ_[l]ˣ) = 0 := by
  have := Lg_mul (1 : ℤ_[l]ˣ) 1
  rw [mul_one] at this
  linear_combination -this

theorem Lg_inv (u : ℤ_[l]ˣ) : large₂ u⁻¹ = -large₂ u := by
  have := Lg_mul u u⁻¹
  rw [mul_inv_cancel, Lg_one] at this
  linear_combination -this

theorem Lg_pow (u : ℤ_[l]ˣ) (n : ℕ) : large₂ (u ^ n) = n * large₂ u := by
  induction n with
  | zero => simp [Lg_one]
  | succ n ih => rw [pow_succ, Lg_mul, ih]; push_cast; ring

theorem continuous_Lg : Continuous (large₂ (l := l)) :=
  (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous
    (continuous_subtype_val.comp (Units.continuous_val (M := ℤ_[l]))) norm_coe_unit

theorem norm_Lg {j : ℕ} (h1 : 1 ≤ j) (h2 : l = 2 → 2 ≤ j) (u : ℤ_[l]ˣ)
    (hu : ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) : ‖large₂ u‖ = ‖(u : ℤ_[l]) - 1‖ :=
  (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 j h1 h2 _ hu

theorem Lg_eq_zero_iff (u : ℤ_[l]ˣ) : large₂ u = 0 ↔ ∃ k : ℕ, 0 < k ∧ u ^ k = 1 := by
  constructor
  · intro h
    have h2 := hl.out.two_le
    refine ⟨l * (l - 1), Nat.mul_pos (by omega) (by omega), ?_⟩
    have h3 := norm_Lg (j := 2) (by norm_num) (fun _ => le_rfl) (u ^ (l * (l - 1)))
      (GlobalTheory.PadicLogUnits.norm_unit_pow_sub_one (norm_coe_unit u))
    rw [Lg_pow, h, mul_zero, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at h3
    exact Units.ext h3
  · rintro ⟨k, hk, h⟩
    have := Lg_pow u k
    rw [h, Lg_one, eq_comm, mul_eq_zero] at this
    exact this.resolve_left (by exact_mod_cast hk.ne')

theorem norm_le_iff_dvd (x : ℤ_[l]) (j : ℕ) :
    ‖x‖ ≤ (l : ℝ) ^ (-(j : ℤ)) ↔ (l : ℤ_[l]) ^ j ∣ x := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

theorem exists_teich (a : ℤ_[l]ˣ) :
    ∃ z : ℤ_[l]ˣ, z ^ (l - 1) = 1 ∧ (l : ℤ_[l]) ∣ ((a * z⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  have h2 := hl.out.two_le
  have hF : (l : ℤ_[l]) ∣ (a : ℤ_[l]) ^ (l - 1) - 1 := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_pow, map_one, sub_eq_zero]
    exact ZMod.pow_card_sub_one_eq_one (a.isUnit.map PadicInt.toZMod).ne_zero
  have hd : ‖(((l - 1 : ℕ) : ℤ_[l]))‖ = 1 := by
    have := GlobalTheory.PadicLogUnits.norm_sub_one (l := l)
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Nat.cast_sub hl.out.one_le, Nat.cast_one, this]
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma (p := l)
    (F := (Polynomial.X ^ (l - 1) - 1 : Polynomial ℤ_[l])) (a := (a : ℤ_[l])) (by
      simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, Polynomial.derivative_sub,
        Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero, map_mul, Polynomial.aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply, norm_mul, norm_pow, PadicInt.norm_units, hd]
      simpa using (PadicInt.norm_lt_one_iff_dvd _).2 hF)
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at hz
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hz (by omega)
  obtain ⟨w, rfl⟩ := hzu
  refine ⟨w, Units.ext (by simpa using hz), ?_⟩
  have h3 := (PadicInt.norm_lt_one_iff_dvd _).1 (hza.trans_le (PadicInt.norm_le_one _))
  have e : ((a * w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 = ((w : ℤ_[l]) - a) * (-((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) := by
    rw [Units.val_mul]
    linear_combination w.mul_inv
  rw [e]
  exact h3.mul_right _

section Sub

variable {S : Subgroup ℤ_[l]ˣ} {s d : ℕ}

theorem dvd_pow_sub_one (hS : ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → u ∈ S)
    (hd : ∀ z ∈ S, (∃ k : ℕ, 0 < k ∧ z ^ k = 1) → z ^ d = 1) {a : ℤ_[l]ˣ} (ha : a ∈ S) :
    (l : ℤ_[l]) ∣ ((a ^ d : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  have h2 := hl.out.two_le
  obtain ⟨z, hz, haz⟩ := exists_teich a
  have hzl : ∀ m : ℕ, z ^ (l ^ m) = z := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_mul, ih]
      have e : z ^ l = z ^ (l - 1 + 1) := by rw [Nat.sub_add_cancel hl.out.one_le]
      rw [e, pow_succ, hz, one_mul]
  have h1 : (a * z⁻¹) ^ (l ^ s) ∈ S := by
    apply hS
    have := dvd_sub_pow_of_dvd_sub haz s
    rw [one_pow, pow_succ] at this
    rw [Units.val_pow_eq_pow_val]
    exact (Dvd.intro _ rfl).trans this
  have h3 : z ∈ S := by
    have := S.mul_mem (S.inv_mem h1) (S.pow_mem ha (l ^ s))
    rwa [mul_pow, inv_pow, hzl, mul_inv_rev, inv_inv, inv_mul_cancel_right] at this
  have h4 := hd z h3 ⟨l - 1, by omega, hz⟩
  have h5 : a ^ d = (a * z⁻¹) ^ d := by rw [mul_pow, inv_pow, h4, inv_one, mul_one]
  rw [h5, Units.val_pow_eq_pow_val]
  have := sub_dvd_pow_sub_pow ((a * z⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) 1 d
  rw [one_pow] at this
  exact haz.trans this

theorem mem_of_norm_Lg_lt {j : ℕ} (h1 : 1 ≤ j) (h2 : l = 2 → 2 ≤ j)
    (hS : ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → u ∈ S) {b c : ℤ_[l]ˣ} (hb : b ∈ S)
    (hbj : (l : ℤ_[l]) ^ j ∣ (b : ℤ_[l]) - 1) (hcj : (l : ℤ_[l]) ^ j ∣ (c : ℤ_[l]) - 1)
    (hlt : ‖large₂ c‖ < ‖large₂ b‖) : c ∈ S := by
  have hb0 : large₂ b ≠ 0 := norm_pos_iff.1 ((norm_nonneg _).trans_lt hlt)
  let t : ℤ_[l] := ⟨large₂ c / large₂ b, by
    rw [norm_div]; exact div_le_one_of_le₀ hlt.le (norm_nonneg _)⟩
  have ht := (PadicInt.norm_le_pow_iff_mem_span_pow _ s).2 (PadicInt.appr_spec s t)
  set n := t.appr s
  have hj : (l : ℤ_[l]) ^ j ∣ ((c * (b ^ n)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
    have e : ((c * (b ^ n)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
        (((c : ℤ_[l]) - 1) - ((b : ℤ_[l]) ^ n - 1 ^ n)) * (((b ^ n)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [Units.val_mul, ← Units.val_pow_eq_pow_val, one_pow]
      linear_combination (b ^ n).mul_inv
    rw [e]
    exact (dvd_sub hcj (hbj.trans (sub_dvd_pow_sub_pow _ _ _))).mul_right _
  have h3 := norm_Lg h1 h2 _ ((norm_le_iff_dvd _ _).2 hj)
  have h4 : c * (b ^ n)⁻¹ ∈ S := by
    apply hS
    rw [← norm_le_iff_dvd, ← h3, Lg_mul, Lg_inv, Lg_pow]
    have e : large₂ c + -((n : ℚ_[l]) * large₂ b) = ((t - n : ℤ_[l]) : ℚ_[l]) * large₂ b := by
      rw [PadicInt.coe_sub, PadicInt.coe_natCast]
      change _ = (large₂ c / large₂ b - n) * large₂ b
      field_simp
      ring
    rw [e, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      ((GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_coe_unit b))).trans ht
  have := S.mul_mem h4 (S.pow_mem hb n)
  rwa [inv_mul_cancel_right] at this

theorem two_adic_cases (h : l = 2) (u : ℤ_[l]ˣ) :
    (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 ∨ (l : ℤ_[l]) ^ 2 ∣ ((-u : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  obtain ⟨v, hv⟩ := u.isUnit.map (PadicInt.toZModPow (p := l) 2)
  simp only [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one,
    Units.val_neg, map_neg, ← hv]
  clear hv
  subst h
  revert v
  decide

theorem Lg_neg (u : ℤ_[l]ˣ) : large₂ (-u) = large₂ u := by
  have h : large₂ (-1 : ℤ_[l]ˣ) = 0 := (Lg_eq_zero_iff _).2 ⟨2, by norm_num, by simp⟩
  rw [← neg_one_mul, Lg_mul, h, zero_add]

theorem norm_Lg_le_of_max (hS : ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → u ∈ S)
    (hd0 : d ≠ 0) (hd : ∀ z ∈ S, (∃ k : ℕ, 0 < k ∧ z ^ k = 1) → z ^ d = 1) {a : ℤ_[l]ˣ} (ha : a ∈ S)
    (hmax : ∀ b ∈ S, ‖((b ^ d : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ ≤ ‖((a ^ d : ℤ_[l]ˣ) : ℤ_[l]) - 1‖)
    {b : ℤ_[l]ˣ} (hb : b ∈ S) : ‖large₂ b‖ ≤ ‖large₂ a‖ := by
  have main : ∀ j : ℕ, 1 ≤ j → (l = 2 → 2 ≤ j) →
      (l : ℤ_[l]) ^ j ∣ ((a ^ d : ℤ_[l]ˣ) : ℤ_[l]) - 1 → ‖large₂ b‖ ≤ ‖large₂ a‖ := by
    intro j h1 h2 hj
    rw [← norm_le_iff_dvd] at hj
    have h3 := hmax b hb
    rw [← norm_Lg h1 h2 _ hj, ← norm_Lg h1 h2 _ ((hmax b hb).trans hj), Lg_pow, Lg_pow, norm_mul,
      norm_mul] at h3
    have h4 : 0 < ‖(d : ℚ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hd0)
    exact le_of_mul_le_mul_left h3 h4
  by_cases h : l = 2
  swap
  · exact main 1 le_rfl (fun h' => absurd h' h) (by rw [pow_one]; exact dvd_pow_sub_one hS hd ha)
  by_cases h4 : (l : ℤ_[l]) ^ 2 ∣ ((a ^ d : ℤ_[l]ˣ) : ℤ_[l]) - 1
  · exact main 2 (by norm_num) (fun _ => le_rfl) h4
  have hdv : ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 →
      (l : ℤ_[l]) ^ 2 ∣ ((u ^ d : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
    intro u hu
    have := sub_dvd_pow_sub_pow (u : ℤ_[l]) 1 d
    rw [one_pow] at this
    exact hu.trans this
  have ha' := (two_adic_cases h a).resolve_left fun h' => h4 (hdv a h')
  by_contra hlt
  rw [not_le] at hlt
  have hna : -a ∈ S := by
    rcases two_adic_cases h b with hb' | hb'
    · exact mem_of_norm_Lg_lt (by norm_num) (fun _ => le_rfl) hS hb hb' ha' (by rwa [Lg_neg])
    · refine mem_of_norm_Lg_lt (by norm_num) (fun _ => le_rfl) hS (S.mul_mem hb ha) ?_ ha' ?_
      · have e : ((b * a : ℤ_[l]ˣ) : ℤ_[l]) - 1 = (((-b : ℤ_[l]ˣ) : ℤ_[l]) - 1) * ((-a : ℤ_[l]ˣ) : ℤ_[l]) +
            (((-a : ℤ_[l]ˣ) : ℤ_[l]) - 1) := by
          simp only [Units.val_mul, Units.val_neg]; ring
        rw [e]
        exact dvd_add (hb'.mul_right _) ha'
      · rw [Lg_neg, Lg_mul, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
        exact lt_max_of_lt_left hlt
  have hm1 : (-1 : ℤ_[l]ˣ) ∈ S := by
    have := S.mul_mem hna (S.inv_mem ha)
    rwa [neg_mul, mul_inv_cancel] at this
  have h5 := hd _ hm1 ⟨2, by norm_num, by simp⟩
  have h6 := hdv _ ha'
  rw [neg_pow, h5, one_mul] at h6
  exact h4 h6

end Sub

theorem exists_coord {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (hχ : Continuous χ)
    (g₀ : G) (h0 : large₂ (χ g₀) ≠ 0) (hle : ∀ g, ‖large₂ (χ g)‖ ≤ ‖large₂ (χ g₀)‖) :
    ∃ lam : G →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ large₂ (χ g) = 0) ∧
      ∀ g, lam g = Multiplicative.ofAdd 1 ↔ large₂ (χ g) = large₂ (χ g₀) := by
  let f : G → ℤ_[l] := fun g => ⟨large₂ (χ g) / large₂ (χ g₀), by
    rw [norm_div]; exact div_le_one_of_le₀ (hle g) (norm_nonneg _)⟩
  have hf : Continuous f := ((continuous_Lg.comp hχ).div_const _).subtype_mk _
  refine ⟨MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun a b => ?_,
    continuous_ofAdd.comp hf, fun g => ?_, fun g => ?_⟩
  · rw [← ofAdd_add]
    refine congrArg _ (Subtype.ext ?_)
    change large₂ (χ (a * b)) / large₂ (χ g₀) = large₂ (χ a) / large₂ (χ g₀) + large₂ (χ b) / large₂ (χ g₀)
    rw [map_mul, Lg_mul, add_div]
  · rw [MonoidHom.mk'_apply, ofAdd_eq_one]
    refine Subtype.ext_iff.trans ?_
    change large₂ (χ g) / large₂ (χ g₀) = 0 ↔ _
    rw [div_eq_zero_iff, or_iff_left h0]
  · rw [MonoidHom.mk'_apply, Multiplicative.ofAdd.apply_eq_iff_eq]
    refine Subtype.ext_iff.trans ?_
    change large₂ (χ g) / large₂ (χ g₀) = 1 ↔ _
    rw [div_eq_one_iff_eq h0]

theorem norm_algebraMap_ext (LL : FinExt l) (x : ℚ_[l]) :
    ‖((algebraMap ℚ_[l] ↥LL.1 x : ↥LL.1) : Om l)‖ = ‖x‖ := by
  change ‖algebraMap ℚ_[l] (Om l) x‖ = ‖x‖
  exact norm_algebraMap' _ x

theorem v_eq_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (j : ℤ) :
    P.v LL (algebraMap ℚ_[l] ↥LL.1 x) = ((j : ℚ) : WithTop ℚ) ↔ ‖x‖ = (l : ℝ) ^ (-j) := by
  rw [(NormVal.locPrime_v_normalised l P LL).1, norm_algebraMap_ext, Rat.cast_intCast,
    ← Int.cast_neg, Real.rpow_intCast]

theorem le_v_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (j : ℤ) :
    ((j : ℚ) : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-j) := by
  rw [(NormVal.locPrime_v_normalised l P LL).2.1, norm_algebraMap_ext, Rat.cast_intCast,
    ← Int.cast_neg, Real.rpow_intCast]

theorem norm_le_of_v_le (P : LocPrime l) (LL : FinExt l) {x y : ℚ_[l]}
    (h : P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y)) : ‖y‖ ≤ ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, map_zero, AddValuation.map_zero, top_le_iff, AddValuation.top_iff,
      map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
    rw [h, norm_zero]
    exact norm_nonneg _
  · have h1 := Padic.norm_eq_zpow_neg_valuation hx
    rw [(v_eq_iff P LL x _).2 h1, le_v_iff] at h
    rwa [h1]

set_option maxHeartbeats 1600000 in

theorem exists_gamma_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ Γ : GamS P K s LL, (∃ lam : ↥Γ.GKs →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ (g : ↥(GK K)) = 1) ∧ (∀ g, lam g = Multiplicative.ofAdd 1 ↔ Γ.resΓ (g : ↥(GK K)) = Γ.gam) ∧ (∃ g, lam g = Multiplicative.ofAdd 1) ∧ IsClosed (Γ.GKs : Set ↥(GK K))) ∧ ∃ lam : ↥(GK K) →* Multiplicative ℤ_[l], Continuous lam ∧ (∀ g, lam g = 1 ↔ Γ.resΓ g ∈ Γ.DelF) ∧ (∀ g, Γ.resΓ g = Γ.gamK → lam g = Multiplicative.ofAdd 1) := by
  intro l hl P K s LL hg Γ
  obtain ⟨hs1, hs2, hK, -⟩ := hg
  obtain ⟨χ₀, hχ₀, hc₀, hon⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  let χ : ↥(GK K) →* ℤ_[l]ˣ := χ₀.comp (GK K).subtype
  have hc : Continuous χ := hc₀.comp continuous_subtype_val
  have hPD : ∀ g, ((P.PD K).χ g : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [P.PD_χ]; exact (hχ₀ _).symm
  have hres : ∀ g, algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) =
      algebraMap ℚ_[l] ↥LL.1 ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by rw [Γ.χΓ_res, hPD]
  have hker : ∀ g, Γ.resΓ g = 1 ↔ χ g = 1 := by
    intro g
    constructor
    · intro h
      have := hres g
      rw [h, Γ.χΓ.map_one, Units.val_one, RingHom.map_one, eq_comm,
        map_eq_one_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at this
      exact Units.ext (Subtype.ext this)
    · intro h
      have := hres g
      rw [h, Units.val_one, PadicInt.coe_one, RingHom.map_one] at this
      refine Γ.χΓ_inj (Eq.trans ?_ Γ.χΓ.map_one.symm)
      exact Units.ext (Subtype.ext this)
  have heq : ∀ g g', Γ.resΓ g = Γ.resΓ g' ↔ χ g = χ g' := by
    intro g g'
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hker, map_mul, map_inv, mul_inv_eq_one]
  have hs : ((s : ℕ) : WithTop ℚ) = (((s : ℤ) : ℚ) : WithTop ℚ) := by simp
  have hmem : ∀ g, g ∈ Γ.GKs ↔ ‖(χ g : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
    intro g
    rw [Γ.GKs_def, hPD, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, hs, le_v_iff]
    rfl
  obtain ⟨g₀, hg₀⟩ := Γ.resΓ_onto Γ.gam
  have hn₀ : ‖(χ g₀ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    have := Γ.gam_gen
    rw [← hg₀, hres, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, hs, v_eq_iff] at this
    exact this
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hL₀ : large₂ (χ g₀) ≠ 0 := by
    rw [← norm_pos_iff, norm_Lg hs1 hs2 _ hn₀.le, hn₀]
    positivity
  have hz : ∀ g ∈ Γ.GKs, large₂ (χ g) = 0 ↔ Γ.resΓ g = 1 := by
    intro g hg
    rw [hker, ← norm_eq_zero, norm_Lg hs1 hs2 _ ((hmem g).1 hg), norm_eq_zero, sub_eq_zero,
      Units.val_eq_one]
  have hm₀ : g₀ ∈ Γ.GKs := (hmem g₀).2 hn₀.le
  have hΔ : ∀ g, Γ.resΓ g ∈ Γ.DelF ↔ ∃ k : ℕ, 0 < k ∧ χ g ^ k = 1 := by
    intro g
    simp only [Γ.DelF_def, ← map_pow, hker]
  refine ⟨?_, ?_⟩
  · obtain ⟨lam, h1, h2, h3⟩ := exists_coord (χ.comp Γ.GKs.subtype) (hc.comp continuous_subtype_val)
      ⟨g₀, hm₀⟩ hL₀ (fun g => by
        change ‖large₂ (χ g)‖ ≤ ‖large₂ (χ g₀)‖
        rw [norm_Lg hs1 hs2 _ hn₀.le, hn₀, norm_Lg hs1 hs2 _ ((hmem g).1 g.2)]
        exact (hmem g).1 g.2)
    refine ⟨lam, h1, fun g => (h2 g).trans (hz g g.2), fun g => (h3 g).trans ?_,
      ⟨⟨g₀, hm₀⟩, (h3 _).2 rfl⟩, ?_⟩
    · change large₂ (χ g) = large₂ (χ g₀) ↔ _
      have := hz _ (Γ.GKs.mul_mem g.2 (Γ.GKs.inv_mem hm₀))
      rwa [map_mul, map_inv, Lg_mul, Lg_inv, map_mul, map_inv, mul_inv_eq_one, hg₀,
        ← sub_eq_add_neg, sub_eq_zero] at this
    · have e : (Γ.GKs : Set ↥(GK K)) = {g | ‖(χ g : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ))} :=
        Set.ext hmem
      rw [e]
      exact isClosed_le (((Units.continuous_val (M := ℤ_[l])).comp hc).sub continuous_const).norm
        continuous_const
  · obtain ⟨g₁, hg₁⟩ := Γ.resΓ_onto Γ.gamK
    have hcard : Γ.DelF.card = Nat.card (CommGroup.torsion Γ.Gam) := by
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      rw [Γ.DelF_def, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    have hle : ∀ g, ‖large₂ (χ g)‖ ≤ ‖large₂ (χ g₁)‖ := by
      intro g
      refine norm_Lg_le_of_max (S := χ.range) (s := s) (d := Γ.DelF.card) ?_ ?_ ?_ ⟨g₁, rfl⟩ ?_
        ⟨g, rfl⟩
      · intro u hu
        obtain ⟨g, hg, h⟩ := hon K s hK u hu
        exact ⟨⟨g, hg⟩, h⟩
      · exact Finset.card_ne_zero_of_mem ((Γ.DelF_def 1).2 ⟨1, one_pos, one_pow _⟩)
      · rintro _ ⟨g, rfl⟩ hz
        have h1 := (Γ.DelF_def _).1 ((hΔ g).2 hz)
        rw [← isOfFinOrder_iff_pow_eq_one, ← CommGroup.mem_torsion] at h1
        rw [← map_pow, ← hker, map_pow, hcard]
        exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, h1⟩ : CommGroup.torsion Γ.Gam)))
      · rintro _ ⟨g, rfl⟩
        have := Γ.gamK_gen (Γ.resΓ g)
        rw [← hg₁, map_pow, map_pow, hres, hres, ← map_pow, ← map_pow,
          ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, ← map_sub] at this
        exact norm_le_of_v_le P LL this
    have hL₁ : large₂ (χ g₁) ≠ 0 := norm_pos_iff.1 ((norm_pos_iff.2 hL₀).trans_le (hle g₀))
    obtain ⟨lam, h1, h2, h3⟩ := exists_coord χ hc g₁ hL₁ hle
    refine ⟨lam, h1, fun g => ?_, fun g hg => ?_⟩
    · rw [h2, hΔ, Lg_eq_zero_iff]
    · rw [h3, (heq g g₁).1 (hg.trans hg₁.symm)]

end GlobalTheory.HWL.Coord
