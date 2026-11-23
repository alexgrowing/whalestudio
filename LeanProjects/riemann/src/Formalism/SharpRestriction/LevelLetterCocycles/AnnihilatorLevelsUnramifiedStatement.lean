import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsOfGrading
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.LG

open PowerSeries

variable {O : Type} [CommRing O]

theorem exists_trunc_add (f : PowerSeries O) (N : ℕ) :
    ∃ g, f = (trunc N f : PowerSeries O) + X ^ N * g := by
  have h : X ^ N ∣ f - (trunc N f : PowerSeries O) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_coe_trunc_of_lt hm, sub_self]
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [← hg]; ring⟩

theorem algHom_ext_X (τ σ : PowerSeries O →ₐ[O] PowerSeries O) (hX : τ X = σ X)
    (h0 : constantCoeff (τ X) = 0) : τ = σ := by
  have hpoly : ∀ p : Polynomial O, τ (p : PowerSeries O) = σ (p : PowerSeries O) := by
    intro p
    have := congrArg (fun φ : Polynomial O →ₐ[O] PowerSeries O => φ p)
      (Polynomial.algHom_ext (f := τ.comp (Polynomial.coeToPowerSeries.algHom O))
        (g := σ.comp (Polynomial.coeToPowerSeries.algHom O))
        (by simp [Polynomial.coeToPowerSeries.algHom_apply, hX]))
    simpa [Polynomial.coeToPowerSeries.algHom_apply] using this
  have hd : X ∣ τ X := X_dvd_iff.mpr h0
  ext f k
  obtain ⟨g, hg⟩ := exists_trunc_add f (k + 1)
  have h1 : X ^ (k + 1) ∣ τ X ^ (k + 1) * τ g := Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _
  have h2 : X ^ (k + 1) ∣ σ X ^ (k + 1) * σ g := by
    rw [← hX]; exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _
  have hτ : τ f = τ (trunc (k + 1) f : PowerSeries O) + τ X ^ (k + 1) * τ g := by
    conv_lhs => rw [hg]
    rw [map_add, map_mul, map_pow]
  have hσ : σ f = σ (trunc (k + 1) f : PowerSeries O) + σ X ^ (k + 1) * σ g := by
    conv_lhs => rw [hg]
    rw [map_add, map_mul, map_pow]
  rw [hτ, hσ, map_add, map_add, hpoly,
    X_pow_dvd_iff.mp h1 k (Nat.lt_succ_self k), X_pow_dvd_iff.mp h2 k (Nat.lt_succ_self k)]

theorem algHom_eq_subst (τ : PowerSeries O →ₐ[O] PowerSeries O) (h0 : constantCoeff (τ X) = 0)
    (f : PowerSeries O) : τ f = subst (τ X) f := by
  have hs : HasSubst (τ X) := HasSubst.of_constantCoeff_zero' h0
  have := algHom_ext_X τ ((substAlgHom hs).restrictScalars O) (by simp [substAlgHom_X]) h0
  rw [show τ f = ((substAlgHom hs).restrictScalars O) f from DFunLike.congr_fun this f]
  simp [coe_substAlgHom]

theorem cc_map (τ : PowerSeries O →ₐ[O] PowerSeries O) (h0 : constantCoeff (τ X) = 0)
    (f : PowerSeries O) : constantCoeff (τ f) = constantCoeff f := by
  obtain ⟨g, hg⟩ := exists_trunc_add f 1
  have hd : X ∣ τ X := X_dvd_iff.mpr h0
  have e : (trunc 1 f : PowerSeries O) = C (constantCoeff f) := by
    ext m; rcases m with _ | m <;> simp [coeff_C]
  conv_lhs => rw [hg]
  conv_rhs => rw [hg]
  rw [e, map_add, map_mul, map_pow, pow_one, map_add, map_add, map_mul, map_mul, pow_one]
  have : τ (C (constantCoeff f)) = C (constantCoeff f) := τ.commutes _
  rw [this, X_dvd_iff.mp hd, constantCoeff_X]
  ring

section Taylor

open MvPowerSeries in

theorem taylor_two_var (f : PowerSeries O) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) O) ^ 2 ∣
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) O) f -
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O) f -
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O) (derivative O f) *
          MvPowerSeries.X 1 := by
  classical
  rw [MvPowerSeries.X_pow_dvd_iff]
  intro e he
  rw [map_sub, map_sub, coeff_subst_X_zero_add_X_one, coeff_subst_single,
    show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) O) = MvPowerSeries.monomial (Finsupp.single 1 1) 1
      from MvPowerSeries.X_def 1, coeff_mul_monomial]
  have hsplit : e 1 = 0 ∨ e 1 = 1 := by omega
  rcases hsplit with h | h
  · have he0 : e = Finsupp.single 0 (e 0) := by
      ext i; fin_cases i <;> simp [h]
    have hn : ¬ Finsupp.single (1 : Fin 2) 1 ≤ e := by
      intro hle; have := hle 1; simp [h] at this
    rw [if_pos he0, if_neg hn, h]
    simp
  · have hne : ¬ e = Finsupp.single 0 (e 0) := by
      intro h'; have := congrArg (fun x => x 1) h'; simp [h] at this
    have hle : Finsupp.single (1 : Fin 2) 1 ≤ e := by
      intro i; fin_cases i <;> simp [h]
    have hsub : e - Finsupp.single 1 1 = Finsupp.single 0 (e 0) := by
      ext i; fin_cases i <;> simp [h]
    rw [if_neg hne, if_pos hle, hsub, coeff_subst_single, if_pos (by simp), h]
    simp only [Finsupp.single_eq_same, coeff_derivative, Nat.choose_succ_self_right]
    push_cast
    ring

theorem taylor2 (f D : PowerSeries O) (hD : constantCoeff D = 0) :
    ∃ Q, subst (X + D) f = f + D * derivative O f + D ^ 2 * Q := by
  obtain ⟨Q, hQ⟩ := taylor_two_var f
  let b : Fin 2 → MvPowerSeries Unit O := ![(X : PowerSeries O), D]
  have hb : MvPowerSeries.HasSubst b := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i; fin_cases i
    · show PowerSeries.constantCoeff (X : PowerSeries O) = 0
      simp
    · show PowerSeries.constantCoeff D = 0
      exact hD
  have h2 : HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) O) :=
    HasSubst.of_constantCoeff_zero (by simp)
  have hx0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O) :=
    HasSubst.of_constantCoeff_zero (by simp)
  have key := congrArg (MvPowerSeries.subst b) hQ
  have e1 : MvPowerSeries.subst b (PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 :
      MvPowerSeries (Fin 2) O) f) = subst (X + D) f := by
    rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply h2.const hb, PowerSeries.subst_def]
    congr 1
    funext u
    rw [MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
    rfl
  have e0 : ∀ g : PowerSeries O, MvPowerSeries.subst b (PowerSeries.subst (MvPowerSeries.X 0 :
      MvPowerSeries (Fin 2) O) g) = g := by
    intro g
    rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hx0.const hb]
    have : (fun _ : Unit => MvPowerSeries.subst b (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O)) =
        fun _ => (X : PowerSeries O) := by
      funext u; rw [MvPowerSeries.subst_X hb]; rfl
    rw [this, ← PowerSeries.subst_def, X_subst]
  rw [MvPowerSeries.subst_sub hb, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_mul hb, e1, e0, e0,
    MvPowerSeries.subst_mul hb, MvPowerSeries.subst_pow hb, MvPowerSeries.subst_X hb] at key
  refine ⟨MvPowerSeries.subst b Q, ?_⟩
  have : b 1 = D := rfl
  rw [this] at key
  linear_combination key

end Taylor

open PowerSeries

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [BinomialRing R] [Algebra R O]

theorem coeff_bs (r : R) (k : ℕ) :
    coeff k (binomialSeries O r) = algebraMap R O (Ring.choose r k) := by
  rw [binomialSeries_coeff, Algebra.smul_def, mul_one]

theorem choose_rec (r : R) (k : ℕ) :
    ((k : R) + 1) * Ring.choose r (k + 1) + (k : R) * Ring.choose r k = r * Ring.choose r k := by
  have h1 : ∀ j : ℕ, ((j : R) + 1) * Ring.choose r (j + 1) = r * Ring.choose (r - 1) j := by
    intro j
    have := Ring.choose_smul_choose r (Nat.le_add_left 1 j)
    rw [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right, Nat.add_sub_cancel, Nat.cast_one]
      at this
    rw [← this]; push_cast; ring
  rcases k with _ | j
  · have := h1 0
    simp only [Nat.cast_zero, zero_add, one_mul, Ring.choose_zero_right, mul_one, add_zero] at this ⊢
    exact this
  · have e := Ring.choose_succ_succ (r - 1) j
    rw [sub_add_cancel] at e
    have h2 := h1 (j + 1)
    have h3 := h1 j
    push_cast at h2 ⊢
    linear_combination h2 + h3 - r * e

theorem bs_ode (r : R) :
    (1 + X) * derivative O (binomialSeries O r) =
      algebraMap O (PowerSeries O) (algebraMap R O r) * binomialSeries O r := by
  ext k
  rw [add_mul, one_mul, map_add, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rcases k with _ | k
  · rw [coeff_zero_X_mul, add_zero, coeff_derivative, coeff_bs, coeff_bs, Ring.choose_one_right,
      Ring.choose_zero_right, map_one]
    simp
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    simp only [coeff_bs]
    have := congrArg (algebraMap R O) (choose_rec r (k + 1))
    simp only [map_add, map_mul, map_natCast, map_one] at this
    push_cast at this ⊢
    linear_combination this

variable [IsDomain O] [CharZero O]

theorem ode_unique (c : O) {F G : PowerSeries O} (h0 : constantCoeff F = constantCoeff G)
    (hF : (1 + X) * derivative O F = algebraMap O (PowerSeries O) c * F)
    (hG : (1 + X) * derivative O G = algebraMap O (PowerSeries O) c * G) : F = G := by
  have hH : (1 + X) * derivative O (F - G) = algebraMap O (PowerSeries O) c * (F - G) := by
    rw [map_sub]; linear_combination hF - hG
  have key : ∀ k, coeff k (F - G) = 0 := by
    intro k
    induction k with
    | zero => rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0,
        sub_self]
    | succ k ih =>
      have e := congrArg (coeff k) hH
      rw [add_mul, one_mul, map_add, ← Algebra.smul_def, map_smul, smul_eq_mul, ih, mul_zero,
        coeff_derivative] at e
      have hx : coeff k (X * derivative O (F - G)) = 0 := by
        rcases k with _ | j
        · exact coeff_zero_X_mul _
        · rw [coeff_succ_X_mul, coeff_derivative, ih, zero_mul]
      rw [hx, add_zero] at e
      exact (mul_eq_zero.mp e).resolve_right (Nat.cast_add_one_ne_zero k)
  ext k
  have := key k
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem bs_natMul (r : R) : ∀ l : ℕ, binomialSeries O ((l : R) * r) = binomialSeries O r ^ l
  | 0 => by simp
  | l + 1 => by
    rw [show ((l + 1 : ℕ) : R) * r = (l : R) * r + r by push_cast; ring, binomialSeries_add,
      bs_natMul r l, pow_succ]

theorem subst_bs (l : ℕ) (hl : 1 ≤ l) (r : R) :
    subst ((1 + X) ^ l - 1 : PowerSeries O) (binomialSeries O r) = binomialSeries O ((l : R) * r) := by
  have hW0 : constantCoeff ((1 + X) ^ l - 1 : PowerSeries O) = 0 := by simp
  have hs : HasSubst ((1 + X) ^ l - 1 : PowerSeries O) := HasSubst.of_constantCoeff_zero' hW0
  let σ : PowerSeries O →ₐ[O] PowerSeries O := substAlgHom hs
  have hσ : ∀ f, σ f = subst ((1 + X) ^ l - 1 : PowerSeries O) f := fun f =>
    congrFun (coe_substAlgHom hs) f
  have hσX : σ X = (1 + X) ^ l - 1 := substAlgHom_X hs
  have hσ0 : constantCoeff (σ X) = 0 := by rw [hσX]; exact hW0
  rw [← hσ]
  apply ode_unique (algebraMap R O ((l : R) * r))
  · rw [cc_map σ hσ0, binomialSeries_constantCoeff, binomialSeries_constantCoeff]
  · have hd : derivative O ((1 + X) ^ l - 1 : PowerSeries O) = (l : PowerSeries O) * (1 + X) ^ (l - 1) := by
      simp only [map_sub, derivative_pow, map_add, derivative_X, derivative_one, zero_add, mul_one,
        sub_zero]
    have h1 : (1 + X : PowerSeries O) * (1 + X) ^ (l - 1) = (1 + X) ^ l := by
      rw [← pow_succ']; congr 1; omega
    have h2 : σ (1 + X) = (1 + X) ^ l := by rw [map_add, map_one, hσX]; ring
    have h3 : (1 + X) ^ l * σ (derivative O (binomialSeries O r)) =
        algebraMap O (PowerSeries O) (algebraMap R O r) * σ (binomialSeries O r) := by
      have := congrArg σ (bs_ode (O := O) r)
      rw [map_mul, map_mul, h2, AlgHom.commutes] at this
      exact this
    have hdG : derivative O (σ (binomialSeries O r)) =
        σ (derivative O (binomialSeries O r)) * ((l : PowerSeries O) * (1 + X) ^ (l - 1)) := by
      rw [hσ, hσ, derivative_subst hs, hd]
    rw [hdG, map_mul, map_natCast, map_mul, map_natCast]
    calc (1 + X) * (σ (derivative O (binomialSeries O r)) * ((l : PowerSeries O) * (1 + X) ^ (l - 1)))
        = (l : PowerSeries O) * ((1 + X) ^ l * σ (derivative O (binomialSeries O r))) := by
          rw [← h1]; ring
      _ = _ := by rw [h3]; ring
  · exact bs_ode _

theorem func_unique (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (l : ℕ) (hl : 2 ≤ l)
    (hφ : φ₀ X = (1 + X) ^ l - 1) {U V : PowerSeries O}
    (h0U : constantCoeff U = 1) (h0V : constantCoeff V = 1) (h1 : coeff 1 U = coeff 1 V)
    (hU : φ₀ U = U ^ l) (hV : φ₀ V = V ^ l) : U = V := by
  have hW0 : constantCoeff ((1 + X) ^ l - 1 : PowerSeries O) = 0 := by simp
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr hW0
  have hq0 : constantCoeff q = (l : O) := by
    have e := congrArg (coeff 0 ∘ derivative O) hq
    simp only [Function.comp_apply, map_sub, derivative_pow, map_add, derivative_X, derivative_one,
      zero_add, mul_one, sub_zero, Derivation.leibniz, smul_eq_mul] at e
    simp at e
    exact e.symm
  have hφ0 : constantCoeff (φ₀ X) = 0 := by rw [hφ]; exact hW0
  have key : ∀ m : ℕ, X ^ (m + 2) ∣ U - V := by
    intro m
    induction m with
    | zero =>
      rw [X_pow_dvd_iff]
      intro k hk
      rcases k with _ | _ | k
      · rw [map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0U, h0V,
          sub_self]
      · rw [map_sub, h1, sub_self]
      · omega
    | succ m ih =>
      obtain ⟨E, hE⟩ := ih
      have hS := geom_sum₂_mul U V l
      have e1 : φ₀ (U - V) = (X * q) ^ (m + 2) * φ₀ E := by
        rw [hE, map_mul, map_pow, hφ, hq]
      rw [map_sub, hU, hV, ← hS, hE] at e1
      have e2 : (∑ i ∈ Finset.range l, U ^ i * V ^ (l - 1 - i)) * E = q ^ (m + 2) * φ₀ E := by
        apply X_pow_mul_cancel (k := m + 2)
        rw [mul_pow] at e1
        linear_combination e1
      have e3 := congrArg constantCoeff e2
      rw [map_mul, map_mul, map_pow, cc_map φ₀ hφ0, hq0, map_sum] at e3
      simp only [map_mul, map_pow, h0U, h0V, one_pow, mul_one, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul] at e3
      have hne : ((l : O) ^ (m + 2) - l) ≠ 0 := by
        have : l ^ (m + 2) ≠ l := by
          have : l ^ 1 < l ^ (m + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
          rw [pow_one] at this; omega
        intro h
        apply this
        exact_mod_cast sub_eq_zero.mp h
      have hE0 : constantCoeff E = 0 := by
        have : ((l : O) ^ (m + 2) - l) * constantCoeff E = 0 := by linear_combination -e3
        exact (mul_eq_zero.mp this).resolve_left hne
      obtain ⟨E', hE'⟩ := X_dvd_iff.mpr hE0
      exact ⟨E', by rw [hE, hE', pow_succ]; ring⟩
  ext k
  have := X_pow_dvd_iff.mp (key k) k (by omega)
  rw [map_sub, sub_eq_zero] at this
  exact this

section Aut

variable (φ₀ τ : PowerSeries O →ₐ[O] PowerSeries O) (l : ℕ) (hl : 2 ≤ l)
  (hφ : φ₀ X = (1 + X) ^ l - 1)
include hl hφ

theorem phi_bs (r : R) : φ₀ (binomialSeries O r) = binomialSeries O ((l : R) * r) := by
  have h0 : constantCoeff (φ₀ X) = 0 := by rw [hφ]; simp
  rw [algHom_eq_subst φ₀ h0, hφ, subst_bs l (by omega)]

theorem phi_pow_bs : ∀ (k : ℕ) (m : R),
    (φ₀ ^ k) (binomialSeries O m) = binomialSeries O ((l : R) ^ k * m)
  | 0, m => by simp
  | k + 1, m => by
    rw [pow_succ, AlgHom.mul_apply, phi_bs φ₀ l hl hφ, phi_pow_bs k]
    congr 1; ring

theorem phi_pow_X : ∀ k : ℕ, (φ₀ ^ k) X = (1 + X) ^ (l ^ k) - 1
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, AlgHom.mul_apply, hφ, map_sub, map_pow, map_add, map_one, phi_pow_X k,
      show l ^ (k + 1) = l ^ k * l from pow_succ l k, pow_mul]
    ring

variable (hcomm : ∀ a, φ₀ (τ a) = τ (φ₀ a)) (h0 : constantCoeff (τ X) = 0)
include hcomm h0

theorem aut_eq_bs (c : R) (h1 : coeff 1 (τ X) = algebraMap R O c) : 1 + τ X = binomialSeries O c := by
  apply func_unique φ₀ l hl hφ
  · rw [map_add, map_one, h0, add_zero]
  · exact binomialSeries_constantCoeff c
  · rw [map_add, h1, coeff_bs, Ring.choose_one_right, coeff_one, if_neg (by omega), zero_add]
  · rw [map_add, map_one, hcomm, hφ, map_sub, map_pow, map_add, map_one]; ring
  · rw [phi_bs φ₀ l hl hφ, bs_natMul]

theorem aut_core (c m : R) (k : ℕ) (hc : c = 1 + (l : R) ^ k * m)
    (h1 : coeff 1 (τ X) = algebraMap R O c) :
    (∀ f, ∃ H, τ f - f = ((1 + X) ^ (l ^ k) - 1) * H) ∧
    (∀ P Rr : PowerSeries O, P * Rr = (1 + X) ^ (l ^ k) - 1 →
      ∃ H, τ P - algebraMap O (PowerSeries O) (algebraMap R O c) * P = P ^ 2 * H) := by
  set Z : PowerSeries O := (1 + X) ^ (l ^ k) - 1 with hZdef
  set M : PowerSeries O := algebraMap O (PowerSeries O) (algebraMap R O m) with hM
  have hτX := aut_eq_bs φ₀ τ l hl hφ hcomm h0 c h1
  have hB1 : binomialSeries O (1 : R) = 1 + X := by
    have := binomialSeries_nat (A := O) (R := R) 1
    rw [Nat.cast_one, pow_one] at this; exact this
  obtain ⟨E, hE⟩ : X ^ 2 ∣ binomialSeries O m - 1 - M * X := by
    rw [X_pow_dvd_iff]
    intro j hj
    rcases j with _ | _ | j
    · simp [hM]
    · show coeff 1 (binomialSeries O m - 1 - M * X) = 0
      rw [map_sub, map_sub, coeff_bs, Ring.choose_one_right, coeff_one, if_neg one_ne_zero, hM,
        ← Algebra.smul_def, map_smul, coeff_one_X, smul_eq_mul, mul_one]
      ring
    · omega
  have hBm : (φ₀ ^ k) (binomialSeries O m) = 1 + M * Z + Z ^ 2 * (φ₀ ^ k) E := by
    have e : binomialSeries O m = 1 + M * X + X ^ 2 * E := by rw [← hE]; ring
    rw [e, map_add, map_add, map_mul, map_mul, map_pow, map_one, phi_pow_X φ₀ l hl hφ, hM, AlgHom.commutes]
  set E' := (φ₀ ^ k) E
  set D := τ X - X with hDdef
  have hD : D = (1 + X) * (M * Z + Z ^ 2 * E') := by
    have : τ X = binomialSeries O c - 1 := by rw [← hτX]; ring
    rw [hDdef, this, hc, binomialSeries_add, hB1, ← phi_pow_bs φ₀ l hl hφ k m, hBm]
    ring
  have hD0 : constantCoeff D = 0 := by rw [hDdef, map_sub, h0, constantCoeff_X, sub_zero]
  have hτf : ∀ f, ∃ Q, τ f = f + D * derivative O f + D ^ 2 * Q := by
    intro f
    obtain ⟨Q, hQ⟩ := taylor2 f D hD0
    exact ⟨Q, by rw [algHom_eq_subst τ h0, show τ X = X + D by rw [hDdef]; ring, hQ]⟩
  refine ⟨fun f => ?_, fun P Rr hPR => ?_⟩
  · obtain ⟨Q, hQ⟩ := hτf f
    exact ⟨(1 + X) * (M + Z * E') * (derivative O f + D * Q), by rw [hQ, hD]; ring⟩
  · obtain ⟨Q, hQ⟩ := hτf P
    have hN : 1 ≤ l ^ k := Nat.one_le_pow _ _ (by omega)
    have hL : (1 + X) * (P * derivative O Rr + Rr * derivative O P) =
        ((l ^ k : ℕ) : PowerSeries O) * (1 + P * Rr) := by
      have e : derivative O (P * Rr) = P * derivative O Rr + Rr * derivative O P := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      have h1' : (1 + X : PowerSeries O) * (1 + X) ^ (l ^ k - 1) = (1 + X) ^ (l ^ k) := by
        rw [← pow_succ']; congr 1; omega
      rw [← e, hPR, hZdef]
      simp only [map_sub, derivative_pow, map_add, derivative_X, derivative_one, zero_add, mul_one,
        sub_zero]
      rw [← h1']; ring
    have hcc : algebraMap O (PowerSeries O) (algebraMap R O c) = 1 + ((l ^ k : ℕ) : PowerSeries O) * M := by
      rw [hc, map_add, map_mul, map_pow, map_natCast, map_one, map_add, map_one, map_mul, map_pow,
        map_natCast, hM]; push_cast; ring
    rw [← hPR] at hD
    refine ⟨((l ^ k : ℕ) : PowerSeries O) * M * Rr - (1 + X) * M * derivative O Rr +
      (1 + X) * Rr ^ 2 * E' * derivative O P + (1 + X) ^ 2 * (M + P * Rr * E') ^ 2 * Rr ^ 2 * Q, ?_⟩
    linear_combination hQ - P * hcc + (derivative O P + (D + (1 + X) * (M * (P * Rr) + (P * Rr) ^ 2 * E')) * Q) * hD + (M * P) * hL

end Aut

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL Formalism.MainNotions.UnusedSlot80.ToolsR PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section W

variable (W : LocWach PD LL O v n)

theorem φ₀_X_eq : W.φ₀ X = (1 + X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]

theorem γA_pow_apply (g : W.Gam) (k : ℕ) (a : LetA O n) (i : ZMod n) :
    (W.γA g ^ k) a i = W.γ₀ (g ^ k) (a i) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, ih, pow_succ g k, map_mul, AlgHom.mul_apply]
    rfl

theorem φA_pow_const (c : PowerSeries O) (s : ℕ) :
    (W.φA ^ s) (fun _ => c) = fun _ => (W.φ₀ ^ s) c := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, pow_succ', AlgHom.mul_apply]
    funext i
    simp [LocWach.φA, letφ]

theorem ps_apply (s : ℕ) (i : ZMod n) :
    ps W s i = (W.φ₀ ^ s) (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
  have e : qA W = fun _ => W.π₀₁ + ((PD.p : ℕ) : PowerSeries O) := by
    funext j; simp [qA, lA, LocWach.π₀]
  unfold ps
  rw [e, φA_pow_const]

variable [IsDomain O] [CharZero O]

theorem ps_ne (hR : RingP W) (s : ℕ) (i : ZMod n) : ps W s i ≠ 0 := by
  have hl := two_le (PD := PD)
  intro h
  have h0 : constantCoeff ((W.φ₀ ^ s) X) = 0 := by
    rw [phi_pow_X W.φ₀ PD.p hl (φ₀_X_eq W)]; simp
  have := congrArg constantCoeff h
  rw [ps_apply, cc_map _ h0, map_add, π₀₁_cc hR, zero_add, map_natCast, map_zero] at this
  exact (Nat.cast_ne_zero.mpr (by omega : PD.p ≠ 0)) this

theorem ps_mul_eq (hR : RingP W) (s : ℕ) (i : ZMod n) :
    ∃ Rr : PowerSeries O, ps W s i * Rr = (1 + X) ^ (PD.p ^ (s + 1)) - 1 := by
  have hl := two_le (PD := PD)
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_qP] at hw
  have hq : W.q₀ = (w : LetA O n) i * (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) := by
    have := congrFun hw i
    simpa [LocWach.q, Formalism.MainNotions.WachCoordinates.qP, LocWach.π₀] using this
  refine ⟨(W.φ₀ ^ s) X * (W.φ₀ ^ s) ((w : LetA O n) i), ?_⟩
  rw [← phi_pow_X W.φ₀ PD.p hl (φ₀_X_eq W), pow_succ, AlgHom.mul_apply, W.φ₀_X, hq, ps_apply,
    map_mul, map_mul]
  ring

theorem γA_comm_pow (δ g : W.Gam) (k : ℕ) (a : LetA O n) :
    W.γA δ ((W.γA g ^ k) a) = (W.γA g ^ k) (W.γA δ a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, ih, γA_comm]

theorem levGrad_of {R : Type} [CommRing R] [BinomialRing R] [Algebra R O] (hR : RingP W) (z : R)
    (hz : ((W.χΓ W.gam : Oˣ) : O) = algebraMap R O z) (hz1 : ((PD.p : ℕ) : R) ∣ z - 1) :
    LevGrad W := by
  intro ell s hs
  have hl := two_le (PD := PD)
  set N := PD.p ^ ell with hN
  have h0 := (W.γ₀_X (W.gam ^ N)).1
  have hc1 : coeff 1 (W.γ₀ (W.gam ^ N) X) = algebraMap R O (z ^ N) := by
    rw [(W.γ₀_X (W.gam ^ N)).2, map_pow, Units.val_pow_eq_pow_val, hz, map_pow]
  obtain ⟨m, hm⟩ : ((PD.p : ℕ) : R) ^ (s + 1) ∣ z ^ N - 1 := by
    have := dvd_sub_pow_of_dvd_sub hz1 ell
    rw [one_pow] at this
    exact (pow_dvd_pow _ (by omega)).trans this
  have hc : z ^ N = 1 + ((PD.p : ℕ) : R) ^ (s + 1) * m := by rw [← hm]; ring
  obtain ⟨hA, hB⟩ := aut_core W.φ₀ (W.γ₀ (W.gam ^ N)) PD.p hl (φ₀_X_eq W) (W.γ₀_comm _) h0
    (z ^ N) m (s + 1) hc hc1
  choose Rr hRr using ps_mul_eq W hR s
  have hπ : W.π₀ ∈ W.AΔ := hR.1
  have hpsΔ : ps W s ∈ W.AΔ := ps_mem W hπ s
  have hpsne : ∀ i, ps W s i ≠ 0 := ps_ne W hR s
  have hchi : (chiL W ell : O) = algebraMap R O (z ^ N) := by
    rw [chiL, show ((PD.p : ℤ) ^ ell) = ((N : ℕ) : ℤ) by rw [hN]; push_cast; ring, zpow_natCast,
      Units.val_pow_eq_pow_val, hz, map_pow]
  constructor
  · intro g hg
    choose H hH using fun i => hA (g i)
    have key : (W.γA W.gam ^ N) g - g = ps W s * fun i => Rr i * H i := by
      funext i
      simp only [Pi.sub_apply, Pi.mul_apply]
      rw [γA_pow_apply, hH i, ← hRr i]
      ring
    refine ⟨fun i => Rr i * H i, ?_, key⟩
    apply cancel_AΔ hpsΔ hpsne
    rw [← key]
    exact Subalgebra.sub_mem _ (γA_pow_mem W _ N hg) hg
  · choose H hH using fun i => hB (ps W s i) (Rr i) (hRr i)
    have key : (W.γA W.gam ^ N) (ps W s) - algebraMap O (LetA O n) (chiL W ell : O) * ps W s =
        ps W s ^ 2 * fun i => H i := by
      funext i
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.algebraMap_apply]
      rw [γA_pow_apply, hchi, hH i]
    refine ⟨fun i => H i, ?_, key⟩
    apply cancel_AΔ (Subalgebra.pow_mem _ hpsΔ 2) (fun i => pow_ne_zero 2 (hpsne i))
    rw [← key]
    exact Subalgebra.sub_mem _ (γA_pow_mem W _ N hpsΔ)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hpsΔ)

end W

end Formalism.MainNotions.UnusedSlot80.LG

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

theorem levg_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hg : Good K 1 LL) :
    ∃ z : ℤ_[l], (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)) =
      algebraMap ℤ_[l] ↥(OL LL) z ∧ (((P.PD K).p : ℕ) : ℤ_[l]) ∣ z - 1 := by
  have hp : (P.PD K).p = l := P.PD_p K
  have hs : (H.W K 1 LL hg).s = 1 := H.W_s K 1 LL hg
  obtain ⟨g, hgg⟩ := (H.W K 1 LL hg).resΓ_onto (H.W K 1 LL hg).gam
  have hχ := (H.W K 1 LL hg).χΓ_res g
  rw [hgg] at hχ
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l])) := by
    rw [← hχ]
    exact (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have hint' : IsIntegral ℤ_[l] ((P.PD K).χ g : ℚ_[l]) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective).1 hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  have hzLL : algebraMap ℤ_[l] ↥LL.1 z = algebraMap ↥(OL LL) ↥LL.1
      (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    rw [hχ, ← hz, ← IsScalarTower.algebraMap_apply]
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.val_injective
    exact hzLL.symm
  · have hgen := (H.W K 1 LL hg).gam_gen
    rw [hs, ← hzLL] at hgen
    have hz1 : z - 1 ≠ 0 := by
      intro h0
      have : algebraMap ℤ_[l] ↥LL.1 z - 1 = 0 := by
        rw [← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub, h0, map_zero]
      rw [this, AddValuation.map_zero] at hgen
      exact WithTop.top_ne_natCast 1 hgen
    have hval : (z - 1).valuation = 1 := by
      have h1 := Formalism.MainNotions.CrystallineLiftingInputs.v_padicInt P LL (z - 1) hz1
      rw [map_sub, map_one, hgen] at h1
      exact le_antisymm (Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop h1.ge) (Formalism.MainNotions.RamifiedCoefficientChains.natCast_le_withTop h1.le)
    have e := PadicInt.unitCoeff_spec hz1
    rw [hval, pow_one] at e
    rw [hp]
    exact ⟨_, by rw [e, mul_comm]⟩

theorem levg_charZero {l : ℕ} [Fact l.Prime] (LL : FinExt l) : CharZero ↥(OL LL) :=
  ⟨fun a b h => by
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) h
    simpa using this⟩

theorem killLevFacts_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : KillLevFacts D HW := by
  intro l _ K LL hG hA _
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hA
  obtain ⟨z, hz, hz1⟩ := levg_chi (D.loc l) (HW l) K LL hG
  haveI := levg_charZero LL
  exact Formalism.MainNotions.UnusedSlot80.LG.levGrad_of _ hR z hz hz1

theorem annihilator_levels_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : KillerLevelsTheorem D HW F Cm := fun hAdm =>
  annihilator_levels_of_grading D HW F Cm (killLevFacts_of D HW F hAdm.2) hAdm

end Formalism.MainNotions.UnusedSlot80
