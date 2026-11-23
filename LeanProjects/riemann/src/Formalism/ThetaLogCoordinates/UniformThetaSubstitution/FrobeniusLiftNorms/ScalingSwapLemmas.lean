import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace TwoVariableSwapLemmas

open MvPowerSeries

section Swap

variable {K : Type} [Field K]

def sw (n : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ := Finsupp.equivMapDomain (Equiv.swap 0 1) n

theorem sw_zero (n : Fin 2 →₀ ℕ) : sw n 0 = n 1 := by simp [sw]

theorem sw_one (n : Fin 2 →₀ ℕ) : sw n 1 = n 0 := by simp [sw]

theorem swap_two_eq_rename_equiv (G : MvPowerSeries (Fin 2) K) :
    swap2 G = rename (Equiv.swap (0 : Fin 2) 1).toEmbedding G := by
  rw [rename_eq_subst]
  unfold swap2
  congr 1
  funext i
  fin_cases i <;> simp

theorem coeff_swap2 (G : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) :
    coeff n (swap2 G) = coeff (sw n) G := by
  have h : n = Finsupp.embDomain (Equiv.swap (0 : Fin 2) 1).toEmbedding (sw n) := by
    rw [Finsupp.embDomain_eq_mapDomain, sw, Finsupp.equivMapDomain_eq_mapDomain,
      ← Finsupp.mapDomain_comp]
    have hid : (⇑(Equiv.swap (0 : Fin 2) 1).toEmbedding ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id := by
      funext i
      simp
    rw [hid, Finsupp.mapDomain_id]
  rw [swap_two_eq_rename_equiv]
  conv_lhs => rw [h]
  exact coeff_embDomain_rename _ _ _

theorem swap_two_sub (f g : MvPowerSeries (Fin 2) K) : swap2 (f - g) = swap2 f - swap2 g := by
  simp only [swap_two_eq_rename_equiv, map_sub]

theorem swap_two_C_mul (a : K) (f : MvPowerSeries (Fin 2) K) : swap2 (C a * f) = C a * swap2 f := by
  simp only [swap_two_eq_rename_equiv, map_mul, rename_C]

theorem swap_two_sum {α : Type} (s : Finset α) (f : α → MvPowerSeries (Fin 2) K) :
    swap2 (∑ k ∈ s, f k) = ∑ k ∈ s, swap2 (f k) := by
  simp only [swap_two_eq_rename_equiv, map_sum]

theorem swap_two_map (σ : K →+* K) (f : MvPowerSeries (Fin 2) K) :
    swap2 (map σ f) = map σ (swap2 f) := by
  ext n
  simp only [coeff_swap2, coeff_map]

theorem hasSubst_swap : HasSubst ![(X 1 : MvPowerSeries (Fin 2) K), X 0] := HasSubst.X_X

theorem swap_two_frobenius {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries (Fin 2) K) :
    swap2 (frobVar p f) = frobVar p (swap2 f) := by
  rw [frobVar_eq_expand hp (swap2 f)]
  unfold swap2 frobVar
  rw [expand_subst p hp hasSubst_swap, subst_comp_subst_apply (HasSubst.X_pow hp) hasSubst_swap]
  congr 1
  funext i
  fin_cases i <;> simp [subst_pow hasSubst_swap, subst_X hasSubst_swap]

theorem swap_two_single_mul (f g : PowerSeries K) :
    swap2 (at1 0 f * at1 1 g) = at1 0 g * at1 1 f := by
  ext n
  rw [coeff_swap2, coeff_product_single_variables (by decide) (by decide), coeff_product_single_variables (by decide)
    (by decide), sw_zero, sw_one, mul_comm]

theorem swap_two_de_s {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) (G : MvPowerSeries (Fin 2) K) :
    DeS p σ (swap2 G) = swap2 (DeS p σ G) := by
  unfold DeS
  rw [swap_two_C_mul, swap_two_sub, swap_two_C_mul, swap_two_frobenius hp, swap_two_map]

end Swap

section Scale

variable {K : Type} [Field K]

def sc2 (u v : K) : Fin 2 → MvPowerSeries (Fin 2) K := ![C u * X 0, C v * X 1]

def sc3 (u v : K) : Fin 3 → MvPowerSeries (Fin 3) K := ![C u * X 0, C u * X 1, C v * X 2]

theorem constant_coeff_scale_two (u v : K) (i : Fin 2) : constantCoeff (sc2 u v i) = 0 := by
  fin_cases i <;> simp [sc2]

theorem constant_coeff_scale_three (u v : K) (i : Fin 3) : constantCoeff (sc3 u v i) = 0 := by
  fin_cases i <;> simp [sc3]

theorem has_subst_scale_two (u v : K) : HasSubst (sc2 u v) := hasSubst_of_constantCoeff_zero (constant_coeff_scale_two u v)

theorem has_subst_scale_three (u v : K) : HasSubst (sc3 u v) := hasSubst_of_constantCoeff_zero (constant_coeff_scale_three u v)

theorem subst_scale_three_X_zero (u v : K) : subst (sc3 u v) (X 0 : MvPowerSeries (Fin 3) K) = C u * X 0 := by
  rw [subst_X (has_subst_scale_three u v)]
  rfl

theorem subst_scale_three_X_one (u v : K) : subst (sc3 u v) (X 1 : MvPowerSeries (Fin 3) K) = C u * X 1 := by
  rw [subst_X (has_subst_scale_three u v)]
  rfl

theorem subst_scale_three_X_two (u v : K) : subst (sc3 u v) (X 2 : MvPowerSeries (Fin 3) K) = C v * X 2 := by
  rw [subst_X (has_subst_scale_three u v)]
  rfl

theorem subst_scale_three_zero (u v : K) : subst (sc3 u v) (0 : MvPowerSeries (Fin 3) K) = 0 := by
  rw [← coe_substAlgHom (has_subst_scale_three u v), map_zero]

theorem subst_scale_two_eq_rescale (u v : K) (H : MvPowerSeries (Fin 2) K) :
    subst (sc2 u v) H = rescale ![u, v] H := by
  rw [rescale_eq_subst]
  congr 1
  funext i
  fin_cases i <;> simp [sc2, smul_eq_C_mul]

theorem coeff_subst_scale_two (u v : K) (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) :
    coeff n (subst (sc2 u v) H) = u ^ n 0 * v ^ n 1 * coeff n H := by
  rw [subst_scale_two_eq_rescale, coeff_rescale, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp

theorem subst_scale_two_comp (u v u' v' : K) (H : MvPowerSeries (Fin 2) K) :
    subst (sc2 u' v') (subst (sc2 u v) H) = subst (sc2 (u * u') (v * v')) H := by
  ext n
  simp only [coeff_subst_scale_two, mul_pow]
  ring

theorem subst_scale_two_one (H : MvPowerSeries (Fin 2) K) : subst (sc2 (1 : K) 1) H = H := by
  ext n
  simp [coeff_subst_scale_two]

theorem swap_two_subst_scale_two (u v : K) (H : MvPowerSeries (Fin 2) K) :
    swap2 (subst (sc2 u v) H) = subst (sc2 v u) (swap2 H) := by
  ext n
  rw [coeff_swap2, coeff_subst_scale_two, coeff_subst_scale_two, coeff_swap2, sw_zero, sw_one]
  ring

theorem has_subst_first_pair : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1] := HasSubst.X_X

theorem constantCoeff_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by
  unfold in3
  exact constantCoeff_subst_eq_zero has_subst_first_pair (by intro i; fin_cases i <;> simp) hF

theorem has_subst_coboundary_first {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    HasSubst ![in3 F, (X 2 : MvPowerSeries (Fin 3) K)] :=
  hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [constantCoeff_first_two_of_three hF])

theorem has_subst_last_pair (x : Fin 3) : HasSubst ![(X x : MvPowerSeries (Fin 3) K), X 2] := HasSubst.X_X

theorem subst_scale_three_include {F : MvPowerSeries (Fin 2) K} {u : K} (v : K)
    (hu : subst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) F = C u * F) :
    subst (sc3 u v) (in3 F) = C u * in3 F := by
  have hs : HasSubst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) :=
    hasSubst_of_constantCoeff_zero (by intro i; simp)
  have h1 : C u * in3 F = in3 (C u * F) := by
    unfold in3
    rw [subst_mul has_subst_first_pair, subst_C]
  rw [h1, ← hu]
  unfold in3
  rw [subst_comp_subst_apply has_subst_first_pair (has_subst_scale_three u v), subst_comp_subst_apply hs has_subst_first_pair]
  congr 1
  funext i
  fin_cases i <;> simp [subst_mul has_subst_first_pair, subst_X has_subst_first_pair, subst_scale_three_X_zero, subst_scale_three_X_one]

theorem partial_coboundary_subst_scale {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) {u : K} (v : K)
    (hu : subst (fun a : Fin 2 => C u * (X a : MvPowerSeries (Fin 2) K)) F = C u * F)
    (H : MvPowerSeries (Fin 2) K) :
    d1 F (subst (sc2 u v) H) = subst (sc3 u v) (d1 F H) := by
  unfold d1
  rw [subst_sub (has_subst_scale_three u v), subst_sub (has_subst_scale_three u v),
    subst_comp_subst_apply (has_subst_scale_two u v) (has_subst_coboundary_first hF), subst_comp_subst_apply (has_subst_scale_two u v) (has_subst_last_pair 0),
    subst_comp_subst_apply (has_subst_scale_two u v) (has_subst_last_pair 1),
    subst_comp_subst_apply (has_subst_coboundary_first hF) (has_subst_scale_three u v), subst_comp_subst_apply (has_subst_last_pair 0) (has_subst_scale_three u v),
    subst_comp_subst_apply (has_subst_last_pair 1) (has_subst_scale_three u v)]
  congr 1
  · congr 1
    · congr 1
      funext i
      fin_cases i <;>
        simp [subst_mul (has_subst_coboundary_first hF), subst_X (has_subst_coboundary_first hF), subst_scale_three_X_two, sc2, subst_scale_three_include v hu]
    · congr 1
      funext i
      fin_cases i <;>
        simp [subst_mul (has_subst_last_pair 0), subst_X (has_subst_last_pair 0), subst_scale_three_X_zero, subst_scale_three_X_two, sc2]
  · congr 1
    funext i
    fin_cases i <;>
      simp [subst_mul (has_subst_last_pair 1), subst_X (has_subst_last_pair 1), subst_scale_three_X_one, subst_scale_three_X_two, sc2]

theorem diffOne_add {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (H H' : MvPowerSeries (Fin 2) K) : d1 F (H + H') = d1 F H + d1 F H' := by
  unfold d1
  rw [subst_add (has_subst_coboundary_first hF), subst_add (has_subst_last_pair 0), subst_add (has_subst_last_pair 1)]
  ring

theorem partial_coboundary_C_mul {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (a : K)
    (H : MvPowerSeries (Fin 2) K) : d1 F (C a * H) = C a * d1 F H := by
  unfold d1
  rw [subst_mul (has_subst_coboundary_first hF), subst_mul (has_subst_last_pair 0), subst_mul (has_subst_last_pair 1), subst_C, subst_C, subst_C]
  ring

theorem partial_coboundary_sum {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) (s : Finset ℕ)
    (f : ℕ → MvPowerSeries (Fin 2) K) : d1 F (∑ k ∈ s, f k) = ∑ k ∈ s, d1 F (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := partial_coboundary_C_mul hF 0 (0 : MvPowerSeries (Fin 2) K)
    simpa using h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, diffOne_add hF, ih]

end Scale

section Sim

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem simeq_iff_sub {ι : Type} (f g : MvPowerSeries ι K) : Simeq f g ↔ Simeq (f - g) 0 := by
  unfold Simeq
  rw [sub_zero]

theorem simeq_sum (hS : SimeqRules) {ι : Type} (s : Finset ℕ) (f : ℕ → MvPowerSeries ι K)
    (h : ∀ k ∈ s, Simeq (f k) 0) : Simeq (∑ k ∈ s, f k) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hS K ι).1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := (hS K ι).2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa using h1

theorem integral_C_mul_X {ι : Type} {u : K} (hu : ‖u‖ ≤ 1) (i : ι) :
    Integral (C u * (X i : MvPowerSeries ι K)) := by
  classical
  intro n
  rw [coeff_C_mul, coeff_X]
  split_ifs
  · simpa using hu
  · simp

theorem integral_scale_two {u v : K} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (i : Fin 2) :
    Integral (sc2 u v i) := by
  fin_cases i
  · exact integral_C_mul_X hu 0
  · exact integral_C_mul_X hv 1

theorem integral_scale_three {u v : K} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (i : Fin 3) :
    Integral (sc3 u v i) := by
  fin_cases i
  · exact integral_C_mul_X hu 0
  · exact integral_C_mul_X hu 1
  · exact integral_C_mul_X hv 2

theorem norm_of_pow_eq_one {u : K} {N : ℕ} (hN : N ≠ 0) (h : u ^ N = 1) : ‖u‖ = 1 := by
  have h1 : ‖u‖ ^ N = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) hN).1 h1

end Sim

end TwoVariableSwapLemmas

open TwoVariableSwapLemmas

theorem swap_rules : SwapRules := by
  intro K _ _ p σ G γ γ' hp
  have hp0 : p ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, swap_two_de_s hp0 σ G, ?_⟩
  · ext n
    have hsw : sw (sw n) = n := by
      ext i
      fin_cases i
      · exact (sw_zero _).trans (sw_one _)
      · exact (sw_one _).trans (sw_zero _)
    rw [coeff_swap2, coeff_swap2, hsw]
  · intro h n hn
    rw [coeff_swap2] at hn
    obtain ⟨h0, h1, h2⟩ := h _ hn
    rw [sw_zero, sw_one] at *
    refine ⟨h1, h0, ?_⟩
    have hsq : p * p ≡ 1 [MOD p ^ 2 - 1] := by
      have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      have : p * p = 1 + (p ^ 2 - 1) := by rw [← sq]; omega
      rw [this]
      simp [Nat.ModEq]
    calc n 0 = 1 * n 0 := (one_mul _).symm
      _ ≡ (p * p) * n 0 [MOD p ^ 2 - 1] := (hsq.symm).mul_right _
      _ = p * (p * n 0) := by ring
      _ ≡ p * n 1 [MOD p ^ 2 - 1] := (h2.symm).mul_left _
  · intro h n hn
    rw [coeff_swap2]
    apply h
    rw [sw_zero, sw_one]
    exact hn.symm
  · intro h n
    rw [coeff_swap2]
    exact h _
  · unfold Hser
    rw [swap_two_sub, swap_two_sub, swap_two_C_mul, swap_two_C_mul, swap_two_single_mul, swap_two_single_mul,
      swap_two_de_s hp0]
    ring

theorem LamModule_of (hD : DworkMv) : LamModule := by
  intro K ι _ _ _ _ p σ hp hpn hσ h N hN hs
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlt : ‖(p : K)‖ < 1 := by
    rw [hpn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hr : ‖((N : K))⁻¹‖ = 1 := by
    rw [norm_inv, Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hN, inv_one]
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.C ((N : K)⁻¹) * h) = 0 := by
    simp [h0]
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K ι p σ hp hpn hσ _ h0']
  have hc := (hD K ι p σ hp hpn hσ h h0).1 hI
  intro n
  have he : frobVar p (MvPowerSeries.map σ (MvPowerSeries.C ((N : K)⁻¹) * h)) -
      MvPowerSeries.C (p : K) * (MvPowerSeries.C ((N : K)⁻¹) * h) =
      MvPowerSeries.C ((N : K)⁻¹) *
        (frobVar p (MvPowerSeries.map σ h) - MvPowerSeries.C (p : K) * h) := by
    rw [map_mul, MvPowerSeries.map_C, map_inv₀, map_natCast, frobVar_eq_expand hp0,
      frobVar_eq_expand hp0, map_mul, MvPowerSeries.expand_C]
    ring
  rw [he, MvPowerSeries.coeff_C_mul, norm_mul, hr, one_mul]
  exact hc n

theorem StepZero_of (hM : LamModule) (hS : SimeqRules) (hL : LawSymm) : StepZero := by
  intro K _ _ _ p σ hU hζ F hF be hbe
  obtain ⟨hp, hp2, hpn, -, hσ⟩ := hU
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hdiv, hd1, hd2, hrot⟩ := hbe
  have hF0 : MvPowerSeries.constantCoeff F = 0 := hF.1
  have hsym := (hL K p hp hpn F hF).2.1
  obtain ⟨N, hN⟩ : ∃ N, N = p ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hN] at hζ hrot hsym
  have hsq : p ^ 2 = N + 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    omega
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hsq
    nlinarith
  have hNp : ¬ p ∣ N := by
    intro hd
    have h1 : p ∣ N + 1 := by rw [← hsq]; exact dvd_pow_self p two_ne_zero
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hd).1 h1))
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN0

  have hη : ∀ k : ℕ, (ζ ^ k) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hθ : ∀ k : ℕ, (ζ⁻¹ ^ (p * k)) ^ N = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
  have hηθ : ∀ k : ℕ, (ζ ^ k) ^ p * ζ⁻¹ ^ (p * k) = 1 := fun k => by
    rw [← pow_mul, mul_comm k p, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
  have hηn : ∀ k : ℕ, ‖ζ ^ k‖ ≤ 1 := fun k => (norm_of_pow_eq_one hN0 (hη k)).le
  have hθn : ∀ k : ℕ, ‖ζ⁻¹ ^ (p * k)‖ ≤ 1 := fun k => (norm_of_pow_eq_one hN0 (hθ k)).le

  have havg : ∀ (ι : Type) [Finite ι] (f : ℕ → MvPowerSeries ι K), (∀ k, Simeq (f k) 0) →
      Simeq (MvPowerSeries.C ((N : K)⁻¹) * ∑ k ∈ range N, f k) 0 := fun ι _ f hf =>
    hM K ι p σ hp hpn hσ _ N hNp (simeq_sum hS _ f fun k _ => hf k)

  have hB : ∀ k : ℕ, Simeq (MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be) be := by
    intro k
    have h1 := (hS K (Fin 2)).2.2.2.2 (Fin 2) _ _ (sc2 1 (ζ⁻¹ ^ (p * k))) (constant_coeff_scale_two _ _)
      (integral_scale_two (by simp) (hθn k)) (hrot (ζ ^ k) (hη k))
    have e1 : (![MvPowerSeries.C (ζ ^ k) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) = sc2 (ζ ^ k) 1 := by
      simp [sc2]
    have e2 : (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.C ((ζ ^ k) ^ p) * MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
        sc2 1 ((ζ ^ k) ^ p) := by
      simp [sc2]
    rw [e1, e2, subst_scale_two_comp, subst_scale_two_comp, hηθ k, mul_one, one_mul, one_mul, subst_scale_two_one]
      at h1
    exact h1
  refine ⟨MvPowerSeries.C ((N : K)⁻¹) *
    ∑ k ∈ range N, MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be, ?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have hc : MvPowerSeries.coeff n (MvPowerSeries.C ((N : K)⁻¹) *
        ∑ k ∈ range N, MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be) =
        (N : K)⁻¹ * ((∑ k ∈ range N, (ζ ^ n 0 * ζ⁻¹ ^ (p * n 1)) ^ k) *
          MvPowerSeries.coeff n be) := by
      rw [MvPowerSeries.coeff_C_mul, map_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_subst_scale_two, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm k (n 0),
        mul_assoc p k, mul_assoc p (n 1), mul_comm k (n 1)]
    rw [hc] at hn
    have hbe : MvPowerSeries.coeff n be ≠ 0 := fun h => hn (by rw [h, mul_zero, mul_zero])
    have hsum : ∑ k ∈ range N, (ζ ^ n 0 * ζ⁻¹ ^ (p * n 1)) ^ k ≠ 0 :=
      fun h => hn (by rw [h, zero_mul, mul_zero])
    have hω : ζ ^ n 0 * ζ⁻¹ ^ (p * n 1) = 1 := by
      by_contra hne
      apply hsum
      rw [geom_sum_eq hne, mul_pow, ← pow_mul, ← pow_mul, mul_comm (n 0), mul_comm (p * n 1),
        pow_mul, pow_mul ζ⁻¹, inv_pow, hζ.pow_eq_one]
      simp
    rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hζ0)] at hω
    refine ⟨?_, ?_, ?_⟩
    · by_contra h
      exact hbe (hdiv n (Or.inl (by omega)))
    · by_contra h
      exact hbe (hdiv n (Or.inr (by omega)))
    · rw [← hN, Nat.modEq_iff_dvd, ← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ hζ0, zpow_natCast,
        zpow_natCast, hω, div_self (pow_ne_zero _ hζ0)]
  ·
    rw [simeq_iff_sub]
    have he : MvPowerSeries.C ((N : K)⁻¹) *
        ∑ k ∈ range N, MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be - be =
        MvPowerSeries.C ((N : K)⁻¹) *
          ∑ k ∈ range N, (MvPowerSeries.subst (sc2 (ζ ^ k) (ζ⁻¹ ^ (p * k))) be - be) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, mul_sub, nsmul_eq_mul, ← mul_assoc,
        ← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K)) N, ← map_mul, inv_mul_cancel₀ hNK,
        map_one, one_mul]
    rw [he]
    exact havg (Fin 2) _ fun k => (simeq_iff_sub _ _).1 (hB k)
  ·
    rw [partial_coboundary_C_mul hF0, partial_coboundary_sum hF0]
    apply havg (Fin 3)
    intro k
    rw [partial_coboundary_subst_scale hF0 _ (hsym _ (hη k))]
    have h1 := (hS K (Fin 3)).2.2.2.2 (Fin 3) _ _ (sc3 (ζ ^ k) (ζ⁻¹ ^ (p * k))) (constant_coeff_scale_three _ _)
      (integral_scale_three (hηn k) (hθn k)) hd1
    rwa [subst_scale_three_zero] at h1
  ·
    rw [swap_two_C_mul, swap_two_sum, partial_coboundary_C_mul hF0, partial_coboundary_sum hF0]
    apply havg (Fin 3)
    intro k
    rw [swap_two_subst_scale_two, partial_coboundary_subst_scale hF0 _ (hsym _ (hθ k))]
    have h1 := (hS K (Fin 3)).2.2.2.2 (Fin 3) _ _ (sc3 (ζ⁻¹ ^ (p * k)) (ζ ^ k)) (constant_coeff_scale_three _ _)
      (integral_scale_three (hθn k) (hηn k)) hd2
    rwa [subst_scale_three_zero] at h1

theorem mapSimeq_statement : MapSimeq := by
  intro K0 K ι _ _ _ _ j hj
  refine ⟨?_, ?_⟩
  · rintro f g ⟨h0, hI⟩
    have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.map j f - MvPowerSeries.map j g) = 0 := by
      rw [← map_sub, MvPowerSeries.constantCoeff_map, h0, map_zero]
    refine ⟨h0', ?_⟩
    have hm : MvPowerSeries.map j (mvExp (f - g)) = mvExp (MvPowerSeries.map j (f - g)) := by
      unfold mvExp
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0),
        PowerSeries.map_exp]
    rw [← map_sub, ← hm]
    intro n
    rw [MvPowerSeries.coeff_map, hj]
    exact hI n
  · intro p c c'
    have hA : MvPowerSeries.map j (Aser K0 p) = Aser K p := by
      ext n
      rw [MvPowerSeries.coeff_map]
      simp only [Aser, MvPowerSeries.coeff_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hA' : MvPowerSeries.map j (Aser' K0 p) = Aser' K p := by
      ext n
      rw [MvPowerSeries.coeff_map]
      simp only [Aser', MvPowerSeries.coeff_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    unfold Gser
    rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C, hA, hA']

end Formalism.InvariantFactorPaths.G7
