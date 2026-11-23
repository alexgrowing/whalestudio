import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.UnitLemmaCaseALevelZero

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial

theorem val_zero_of_not_dvd {ℓ : ℕ} [Fact ℓ.Prime] {x : ℤ_[ℓ]} (h : ¬ (ℓ : ℤ_[ℓ]) ∣ x) :
    x ≠ 0 ∧ x.valuation = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact h (dvd_zero _)
  refine ⟨hx0, ?_⟩
  by_contra hv
  obtain ⟨w, hw⟩ := Nat.exists_eq_succ_of_ne_zero hv
  apply h
  rw [PadicInt.unitCoeff_spec hx0, hw, pow_succ]
  exact Dvd.intro_left ((PadicInt.unitCoeff hx0 : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ w) (by ring)

private theorem w3_lemma {ℓ : ℕ} [Fact ℓ.Prime] {z : ℤ_[ℓ]} (hz : z ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) z = (z.valuation : ℕ∞) := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, z = (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ z.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hz⟩
  generalize z.valuation = v at hu ⊢
  rw [emultiplicity_eq_coe]
  constructor
  · rw [hu]
    exact dvd_mul_left _ _
  · rintro ⟨c, hc⟩
    have hne : (ℓ : ℤ_[ℓ]) ^ v ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
    have hcu : (u : ℤ_[ℓ]) = ℓ * c := by
      have h' : (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ v = ((ℓ : ℤ_[ℓ]) * c) * (ℓ : ℤ_[ℓ]) ^ v := by
        rw [← hu, hc]
        ring
      exact mul_right_cancel₀ hne h'
    have hU := u.isUnit
    rw [hcu] at hU
    have h1 := PadicInt.isUnit_iff.mp (isUnit_of_mul_isUnit_left hU)
    rw [PadicInt.norm_p] at h1
    have h2 : (ℓ : ℝ) = 1 := inv_eq_one.mp h1
    exact (Fact.out : ℓ.Prime).one_lt.ne' (by exact_mod_cast h2)

theorem character_value_formula_holds : StatChiVal := by
  intro ℓ _ hℓ χ hχ k hk
  by_cases hdk : (ℓ - 1) ∣ k
  · rw [if_pos hdk]
    obtain ⟨t, rfl⟩ := hdk
    have ht : t ≠ 0 := by
      rintro rfl
      simp at hk
    obtain ⟨a, t', ht', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht ℓ (Fact.out : ℓ.Prime).one_lt.ne'
    have hpr : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p
    have hodd : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ
    have hv1 := hχ.2
    have hw0 : (χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1 ≠ 0 := by
      intro h0
      rw [h0, PadicInt.valuation_zero] at hv1
      exact zero_ne_one hv1
    have hem1 : emultiplicity (ℓ : ℤ_[ℓ]) ((χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1) = 1 := by
      rw [w3_lemma hw0, hv1]
      rfl
    have hdiv : (ℓ : ℤ_[ℓ]) ∣ (χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1 := by
      have := (emultiplicity_eq_coe.mp (by rw [hem1]; rfl : emultiplicity (ℓ : ℤ_[ℓ]) ((χ : ℤ_[ℓ]) ^ (ℓ - 1) - 1) = ((1 : ℕ) : ℕ∞))).1
      simpa using this
    have hwu : ¬ (ℓ : ℤ_[ℓ]) ∣ (χ : ℤ_[ℓ]) ^ (ℓ - 1) := fun h =>
      hpr.not_isUnit (isUnit_of_dvd_unit h ((Units.isUnit χ).pow (ℓ - 1)))
    have hxy : (ℓ : ℤ_[ℓ]) ∣ ((χ : ℤ_[ℓ]) ^ (ℓ - 1)) ^ ℓ ^ a - 1 := by
      refine hdiv.trans ?_
      simpa using sub_dvd_pow_sub_pow ((χ : ℤ_[ℓ]) ^ (ℓ - 1)) 1 (ℓ ^ a)
    have hx : ¬ (ℓ : ℤ_[ℓ]) ∣ ((χ : ℤ_[ℓ]) ^ (ℓ - 1)) ^ ℓ ^ a := fun h => hwu (hpr.dvd_of_dvd_pow h)
    have hn : ¬ (ℓ : ℤ_[ℓ]) ∣ ((t' : ℕ) : ℤ_[ℓ]) := by
      rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff]
      exact ht'
    have e1 := emultiplicity_pow_sub_pow_of_prime hpr hxy hx hn
    have e2 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hpr hodd (y := 1) (by simpa using hdiv)
      (by simpa using hwu) a
    rw [one_pow] at e1 e2
    have key : emultiplicity (ℓ : ℤ_[ℓ]) ((χ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ ^ a * t')) - 1) = ((1 + a : ℕ) : ℕ∞) := by
      rw [pow_mul, pow_mul, e1, e2, hem1]
      push_cast
      ring
    have hne : (χ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ ^ a * t')) - 1 ≠ 0 := by
      intro h0
      rw [h0, emultiplicity_zero] at key
      exact ENat.top_ne_natCast _ key
    refine ⟨hne, ?_⟩
    have hv := w3_lemma hne
    rw [key] at hv
    have hv' : PadicInt.valuation ((χ : ℤ_[ℓ]) ^ ((ℓ - 1) * (ℓ ^ a * t')) - 1) = 1 + a := by
      exact_mod_cast hv.symm
    rw [hv']
    have hl1 : ℓ - 1 ≠ 0 := by have := (Fact.out : ℓ.Prime).two_le; omega
    have ht0 : t' ≠ 0 := by
      rintro rfl
      exact ht' (dvd_zero _)
    rw [padicValNat.mul hl1 (mul_ne_zero (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero) ht0),
      padicValNat.mul (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero) ht0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ht',
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
    ring
  · rw [if_neg hdk]
    exact val_zero_of_not_dvd (fun h => hdk (hχ.1 k h))

private theorem w3_lemma_2 {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {G : GBase ℓ A}
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) {a : A} (b : A) (h : P.Kills a) : P.Kills (b * a) := by
  intro n hn
  rw [mul_smul]
  exact P.N'.smul_mem b (h n hn)

private theorem w3_lemma_3 {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] (G : GBase ℓ A)
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (c : ℤ_[ℓ]) (j : ℕ) (h : P.Kills (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1))) :
    P.Kills (algebraMap ℤ_[ℓ] A (c * ((G.u : ℤ_[ℓ]) ^ (j + 1) - 1)) * G.X ^ j) := by
  intro n hn
  rw [map_mul, map_sub, map_pow, map_one]
  obtain ⟨t, ht⟩ := G.γX
  have hA : (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) • n ∈ P.N' := h n hn
  have hXy : G.X • ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) ∈ P.N' := by
    rw [smul_smul]
    have := h n hn
    rwa [show algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1) = G.X * (algebraMap ℤ_[ℓ] A c * G.X ^ j) by ring] at this
  obtain ⟨z, hz, hzeq⟩ := P.γ_N' _ hXy
  obtain ⟨n', hn', hn'eq⟩ := P.γ_N n hn
  have hγn : P.γ n = n + G.X • n' := by
    rw [← hn'eq]
    abel
  have hγy : P.γ ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) =
      (algebraMap ℤ_[ℓ] A c * (G.X * (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t)) ^ j) • (n + G.X • n') := by
    rw [P.γ_smul, map_mul, map_pow, ht, hγn, AlgHom.commutes]
  have h1 : G.X • ((algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t) • P.γ ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) -
      (algebraMap ℤ_[ℓ] A c * G.X ^ j) • n - z) = 0 := by
    rw [smul_sub, smul_sub, smul_smul, ← ht, ← P.γ_smul, ← hzeq]
    abel
  have h2 : (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t) • P.γ ((algebraMap ℤ_[ℓ] A c * G.X ^ j) • n) -
      (algebraMap ℤ_[ℓ] A c * G.X ^ j) • n = z := by
    have := P.X_inj _ h1
    rwa [sub_eq_zero] at this
  obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) + G.X * t)
    (algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ])) (j + 1)
  have hB : (algebraMap ℤ_[ℓ] A c * G.X ^ (j + 1)) • n' ∈ P.N' := h n' hn'
  rw [hγy] at h2
  generalize algebraMap ℤ_[ℓ] A (G.u : ℤ_[ℓ]) = u' at h2 hr ⊢
  generalize algebraMap ℤ_[ℓ] A c = c' at h2 hA hB ⊢
  have hr' : (u' + G.X * t) ^ (j + 1) = u' ^ (j + 1) + G.X * (t * r) := by
    rw [sub_eq_iff_eq_add] at hr
    rw [hr]
    ring
  generalize u' + G.X * t = q at h2 hr'
  have key : (c' * (u' ^ (j + 1) - 1) * G.X ^ j) • n =
      z - (t * r) • ((c' * G.X ^ (j + 1)) • n) - q ^ (j + 1) • ((c' * G.X ^ (j + 1)) • n') := by
    rw [← h2]
    linear_combination (norm := module) (-(c' * G.X ^ j) * hr') • n
  rw [key]
  exact P.N'.sub_mem (P.N'.sub_mem hz (P.N'.smul_mem _ hA)) (P.N'.smul_mem _ hB)

private theorem w3_lemma_4 {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {G : GBase ℓ A}
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (P : GPair G D) (s j : ℕ) (hjs : j ≤ s) (h : P.Kills (G.X ^ s)) :
    P.Kills (algebraMap ℤ_[ℓ] A (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ j) := by
  have main : ∀ d, d ≤ s - j → P.Kills (algebraMap ℤ_[ℓ] A
      (∏ k ∈ Finset.Ioc (s - d) s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ (s - d)) := by
    intro d
    induction d with
    | zero =>
      intro _
      simpa using h
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have hsd : s - d = (s - (d + 1)) + 1 := by omega
      rw [hsd] at h1
      have h2 := w3_lemma_3 G P _ (s - (d + 1)) h1
      have hmem : s - (d + 1) + 1 ∈ Finset.Ioc (s - (d + 1)) s := by
        simp only [Finset.mem_Ioc]
        omega
      have hprod : ∏ k ∈ Finset.Ioc (s - (d + 1)) s, ((G.u : ℤ_[ℓ]) ^ k - 1) =
          (∏ k ∈ Finset.Ioc (s - (d + 1) + 1) s, ((G.u : ℤ_[ℓ]) ^ k - 1)) *
            ((G.u : ℤ_[ℓ]) ^ (s - (d + 1) + 1) - 1) := by
        rw [← Finset.mul_prod_erase _ _ hmem, mul_comm]
        congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl)
        ext x
        simp only [Finset.mem_erase, Finset.mem_Ioc]
        omega
      rw [hprod]
      exact h2
  have := main (s - j) le_rfl
  rwa [show s - (s - j) = j by omega] at this

theorem cost_bound_kills_obstruction : StatCostKills := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P s j hgen hjs h
  have hd := w3_lemma_4 P s j hjs h
  have hfac : ∀ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1) ≠ 0 ∧
      PadicInt.valuation ((G.u : ℤ_[ℓ]) ^ k - 1) = if (ℓ - 1) ∣ k then 1 + padicValNat ℓ k else 0 := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    exact character_value_formula_holds ℓ hℓ G.u hgen k (by omega)
  have hPr0 : ∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk => (hfac k hk).1)
  have hval : (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)).valuation = cost ℓ j s := by
    have e := Finset.emultiplicity_prod PadicInt.prime_p (Finset.Ioc j s) (fun k => (G.u : ℤ_[ℓ]) ^ k - 1)
    rw [w3_lemma hPr0, Finset.sum_congr rfl (fun k hk => by rw [w3_lemma (hfac k hk).1, (hfac k hk).2])] at e
    unfold cost
    exact_mod_cast e
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, ∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1) =
      (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ cost ℓ j s :=
    ⟨PadicInt.unitCoeff hPr0, by rw [← hval]; exact PadicInt.unitCoeff_spec hPr0⟩
  have heq : (ℓ : A) ^ cost ℓ j s * G.X ^ j = algebraMap ℤ_[ℓ] A ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) *
      (algebraMap ℤ_[ℓ] A (∏ k ∈ Finset.Ioc j s, ((G.u : ℤ_[ℓ]) ^ k - 1)) * G.X ^ j) := by
    rw [hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow, map_natCast]
  rw [heq]
  exact w3_lemma_2 P _ hd

theorem first_descent_of_cost_bound (hB : StatCostBound) : Stat1 := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P s H a j hgen hsH hk ha
  by_cases hjs : j ≤ s
  · have hc := cost_bound_kills_obstruction ℓ hℓ A G D P s j hgen hjs hk
    have hb := hB ℓ hℓ j s H hjs hsH
    have hcw : 1 + Real.logb ℓ ((H : ℝ) + 1) ≤ (cW ℓ H : ℝ) := by
      unfold cW
      exact Nat.le_ceil _
    have hlt : (cost ℓ j s : ℝ) < a := by linarith
    have hle : cost ℓ j s ≤ a := by exact_mod_cast hlt.le
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [show (ℓ : A) ^ (cost ℓ j s + e) * G.X ^ j = (ℓ : A) ^ e * ((ℓ : A) ^ cost ℓ j s * G.X ^ j) by ring]
    exact w3_lemma_2 P _ hc
  · push Not at hjs
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hjs
    rw [show (ℓ : A) ^ a * G.X ^ (s + e + 1) = ((ℓ : A) ^ a * G.X ^ (e + 1)) * G.X ^ s by ring]
    exact w3_lemma_2 P _ hk

theorem wA_of (h1 : Stat1) : StatWA := by
  intro ℓ _ hℓ A _ _ G D _ _ _ _ P H hgen hk
  suffices hnum : ((H : ℝ) - ((0 : ℕ) : ℝ)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + cW ℓ H ≤ (eWA ℓ H : ℝ) by
    simpa using h1 ℓ hℓ A G D P H H (eWA ℓ H) 0 hgen le_rfl hk hnum
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hlog : 0 ≤ Real.logb ℓ ((H : ℝ) + 1) := Real.logb_nonneg hl (by linarith)
  have hc : (cW ℓ H : ℝ) < 1 + Real.logb ℓ ((H : ℝ) + 1) + 1 := by
    unfold cW
    exact Nat.ceil_lt_add_one (by linarith)
  have hq : 0 ≤ (H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 := div_nonneg (mul_nonneg hH (by linarith)) (sq_nonneg _)
  have hf : (H : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 3 + Real.logb ℓ ((H : ℝ) + 1) < (eWA ℓ H : ℝ) + 1 := by
    unfold eWA
    exact Nat.lt_floor_add_one _
  simp only [Nat.cast_zero, sub_zero]
  linarith

theorem second_descent_free_part_holds : Stat2Free := by
  intro ℓ A _ D D' _ _ _ _ S hPP hgen hl hind x hx hφx
  let T : Set D' := {w | ∃ y : Fin ℓ → D, (∀ k, y k ∈ S.P') ∧ w = ∑ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ (y k)}
  have hT0 : (0 : D') ∈ T := ⟨0, fun _ => S.P'.zero_mem, by simp⟩
  have hTadd : ∀ w₁ ∈ T, ∀ w₂ ∈ T, w₁ + w₂ ∈ T := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    exact ⟨y₁ + y₂, fun k => S.P'.add_mem (hy₁ k) (hy₂ k), by
      simp [map_add, smul_add, Finset.sum_add_distrib]⟩
  have hTsum : ∀ (s : Finset (Fin ℓ)) (f : Fin ℓ → D'), (∀ k ∈ s, f k ∈ T) → ∑ k ∈ s, f k ∈ T := by
    intro s f
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hT0
    | insert a s ha ih =>
      intro hf
      rw [Finset.sum_insert ha]
      exact hTadd _ (hf a (Finset.mem_insert_self a s)) _
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
  have hL : ∀ (g : A) (y : D), y ∈ S.P' → g • S.φ y ∈ T := by
    intro g y hy
    obtain ⟨e, he⟩ := hgen g
    refine ⟨fun k => e k • y, fun k => S.P'.smul_mem _ hy, ?_⟩
    rw [he, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [S.φ_smul, mul_smul]
  have hall : ∀ w ∈ Submodule.span A (S.φ '' (S.P' : Set D)), w ∈ T := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      simpa using hL 1 y hy
    | zero => exact hT0
    | add w₁ w₂ _ _ h₁ h₂ => exact hTadd _ h₁ _ h₂
    | smul g w _ hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [Finset.smul_sum]
      refine hTsum _ _ (fun k _ => ?_)
      rw [smul_smul]
      exact hL _ _ (hy k)
  obtain ⟨y, hy, hxy⟩ := hall _ hφx
  let k0 : Fin ℓ := ⟨0, hl⟩
  have hx' : ∀ k, (if k = k0 then x else 0) - y k ∈ S.P := by
    intro k
    refine S.P.sub_mem ?_ (hPP (hy k))
    split_ifs
    · exact hx
    · exact S.P.zero_mem
  have hterm : ∀ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ (if k = k0 then x else 0) = if k = k0 then S.φ x else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      simp [k0]
    · simp
  have hsum : ∑ k : Fin ℓ, S.π ^ (k : ℕ) • S.φ ((fun k => (if k = k0 then x else 0) - y k) k) = 0 := by
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib]
    rw [← hxy, Finset.sum_congr rfl (fun k _ => hterm k)]
    simp
  have h0 := hind (fun k => (if k = k0 then x else 0) - y k) hx' hsum k0
  have hx0 : x = y k0 := by simpa [sub_eq_zero] using h0
  rw [hx0]
  exact hy k0

end Formalism.RepresentationBoundsCohomology.N2
