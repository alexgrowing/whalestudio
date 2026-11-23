import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedDiagonalAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedGaugeEstimate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur

open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RSUnram

noncomputable def hs (α β : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => α ^ (n + 1) + β * hs α β n

theorem hs_zero (α β : ℂ) : hs α β 0 = 1 := rfl

theorem hs_succ (α β : ℂ) (n : ℕ) : hs α β (n + 1) = α ^ (n + 1) + β * hs α β n := rfl

theorem hs_one (α β : ℂ) : hs α β 1 = α + β := by
  simp [hs]

theorem hs_rec (α β : ℂ) (n : ℕ) :
    hs α β (n + 2) = (α + β) * hs α β (n + 1) - α * β * hs α β n := by
  have h1 := hs_succ α β (n + 1)
  have h2 := hs_succ α β n
  rw [h1, h2]
  ring

theorem norm_hs_le {α β : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (n : ℕ) :
    ‖hs α β n‖ ≤ (n : ℝ) + 1 := by
  induction n with
  | zero => simp [hs]
  | succ n ih =>
    rw [hs_succ]
    calc ‖α ^ (n + 1) + β * hs α β n‖ ≤ ‖α ^ (n + 1)‖ + ‖β * hs α β n‖ := norm_add_le _ _
      _ ≤ 1 + ((n : ℝ) + 1) := by
        rw [norm_pow, hα, one_pow, norm_mul, hβ, one_mul]
        linarith
      _ = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

theorem conj_eq_inv {α : ℂ} (hα : ‖α‖ = 1) : conj α = α⁻¹ := by
  have h0 : α ≠ 0 := by
    intro h
    simp [h] at hα
  have h := Complex.mul_conj' α
  rw [hα] at h
  field_simp
  simpa [mul_comm] using h

theorem conj_hs {α β : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (n : ℕ) :
    conj (hs α β n) = ((α * β)⁻¹) ^ n * hs α β n := by
  have h0 : α ≠ 0 := by
    intro h
    simp [h] at hα
  have h1 : β ≠ 0 := by
    intro h
    simp [h] at hβ
  induction n using Nat.twoStepInduction with
  | zero => simp [hs]
  | one =>
    rw [hs_one, map_add, conj_eq_inv hα, conj_eq_inv hβ]
    field_simp
    ring
  | more n ih1 ih2 =>
    obtain ⟨d, hd, e1, e2⟩ : ∃ d, d = (α * β)⁻¹ ∧ α⁻¹ = d * β ∧ β⁻¹ = d * α :=
      ⟨_, rfl, by field_simp, by field_simp⟩
    rw [hs_rec, map_sub, map_mul, map_mul, map_mul, map_add, ih1, ih2, conj_eq_inv hα, conj_eq_inv hβ,
      ← hd, e1, e2]
    ring

theorem summable_sq_mul_geom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 2) ^ 2 * r ^ n := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg h0]
  have a2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have a1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have a0 := summable_pow_mul_geometric_of_norm_lt_one 0 hr
  refine ((a2.add (a1.mul_left 4)).add (a0.mul_left 4)).congr fun n => ?_
  simp only [pow_one, pow_zero]
  ring

theorem tsum_hs_sq {α β x : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hx : ‖x‖ < 1) :
    (Summable fun n => hs α β n ^ 2 * x ^ n) ∧
    (∑' n, hs α β n ^ 2 * x ^ n) * ((1 - α * β * x) * (1 - α ^ 2 * x) * (1 - β ^ 2 * x)) =
      1 + α * β * x := by
  set H := hs α β with hH
  set u : ℕ → ℂ := fun n => H n ^ 2 * x ^ n with hu
  set v : ℕ → ℂ := fun n => H n * H (n + 1) * x ^ n with hv
  have hS := summable_sq_mul_geom (norm_nonneg x) hx
  have hn : ∀ n, ‖H n‖ ≤ (n : ℝ) + 2 := fun n => (norm_hs_le hα hβ n).trans (by linarith)
  have hn' : ∀ n, ‖H (n + 1)‖ ≤ (n : ℝ) + 2 := fun n => by
    have := norm_hs_le hα hβ (n + 1)
    push_cast at this
    linarith
  have su : Summable u := by
    refine Summable.of_norm_bounded hS fun n => ?_
    simp only [hu, norm_mul, norm_pow]
    gcongr
    exact hn n
  have sv : Summable v := by
    refine Summable.of_norm_bounded hS fun n => ?_
    simp only [hv, norm_mul, norm_pow]
    rw [sq]
    gcongr
    · exact hn n
    · exact hn' n
  refine ⟨su, ?_⟩
  set A := ∑' n, u n with hA
  set B := ∑' n, v n with hB
  set a := α + β with ha
  set b := α * β with hb
  have h0 : H 0 = 1 := rfl
  have h1 : H 1 = a := hs_one α β
  have hr : ∀ n, H (n + 2) = a * H (n + 1) - b * H n := hs_rec α β
  have su1 : Summable fun n => u (n + 1) := (summable_nat_add_iff 1).2 su
  have su2 : Summable fun n => u (n + 2) := (summable_nat_add_iff 2).2 su
  have sv1 : Summable fun n => v (n + 1) := (summable_nat_add_iff 1).2 sv
  have tu1 : ∑' n, u (n + 1) = A - u 0 := by
    have := su.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at this
    rw [hA, ← this]
    ring
  have tu2 : ∑' n, u (n + 2) = A - u 0 - u 1 := by
    have := su.sum_add_tsum_nat_add 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    rw [hA, ← this]
    ring
  have tv1 : ∑' n, v (n + 1) = B - v 0 := by
    have := sv.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at this
    rw [hB, ← this]
    ring
  have u0 : u 0 = 1 := by simp [hu, h0]
  have u1 : u 1 = a ^ 2 * x := by simp [hu, h1]
  have v0 : v 0 = a := by simp [hv, h0, h1]
  have e1 : ∀ n, u (n + 2) = a ^ 2 * x * u (n + 1) - 2 * a * b * x ^ 2 * v n + b ^ 2 * x ^ 2 * u n := by
    intro n
    simp only [hu, hv, hr n]
    ring
  have e2 : ∀ n, v (n + 1) = a * u (n + 1) - b * x * v n := by
    intro n
    simp only [hu, hv, hr n]
    ring
  have E1 : A - 1 - a ^ 2 * x = a ^ 2 * x * (A - 1) - 2 * a * b * x ^ 2 * B + b ^ 2 * x ^ 2 * A := by
    have : ∑' n, u (n + 2) =
        ∑' n, (a ^ 2 * x * u (n + 1) - 2 * a * b * x ^ 2 * v n + b ^ 2 * x ^ 2 * u n) := tsum_congr e1
    rw [tu2, u0, u1, ((su1.mul_left _).sub (sv.mul_left _)).tsum_add (su.mul_left _),
      (su1.mul_left _).tsum_sub (sv.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left, tu1, u0] at this
    exact this
  have E2 : B - a = a * (A - 1) - b * x * B := by
    have : ∑' n, v (n + 1) = ∑' n, (a * u (n + 1) - b * x * v n) := tsum_congr e2
    rw [tv1, v0, (su1.mul_left _).tsum_sub (sv.mul_left _), tsum_mul_left, tsum_mul_left, tu1, u0] at this
    exact this
  have hfac : (1 - b * x) * (1 - α ^ 2 * x) * (1 - β ^ 2 * x) =
      1 + (b - a ^ 2) * x + (a ^ 2 * b - b ^ 2) * x ^ 2 - b ^ 3 * x ^ 3 := by
    simp only [ha, hb]
    ring
  rw [hfac]
  linear_combination (1 + b * x) * E1 - 2 * a * b * x ^ 2 * E2

theorem sum_powersetCard_zero (z : Fin 2 → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 0, ∏ i ∈ S, z i = 1 := by
  simp

theorem sum_powersetCard_one (z : Fin 2 → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 1, ∏ i ∈ S, z i = z 0 + z 1 := by
  simp [Finset.powersetCard_one, Fin.sum_univ_two]

theorem sum_powersetCard_two (z : Fin 2 → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 2, ∏ i ∈ S, z i = z 0 * z 1 := by
  have h : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
  simp [h, Fin.prod_univ_two]

theorem sum_powersetCard_big (z : Fin 2 → ℂ) {r : ℕ} (hr : 3 ≤ r) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard r, ∏ i ∈ S, z i = 0 := by
  rw [Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty]

theorem evalAt_schur_row (z : Fin 2 → ℂˣ) (n : ℕ) :
    evalAt z (schur ![(n : ℤ), 0]) = hs (z 0) (z 1) n := by
  obtain ⟨h0, hrec⟩ := GlobalTheory.CompanionTheory.SatakeBound.schur_row_recursion 2 (by norm_num) z
  have hrow : ∀ j : ℕ, (![(j : ℤ), 0] : Fin 2 → ℤ) = Pi.single (⟨0, by norm_num⟩ : Fin 2) (j : ℤ) := by
    intro j
    funext i
    fin_cases i <;> simp
  set T : ℕ → ℂ := fun j => evalAt z (schur (Pi.single (⟨0, by norm_num⟩ : Fin 2) ((j : ℕ) : ℤ))) with hT
  have e0 := sum_powersetCard_zero (fun i => (z i : ℂ))
  have e1 := sum_powersetCard_one (fun i => (z i : ℂ))
  have e2 := sum_powersetCard_two (fun i => (z i : ℂ))
  have T0 : T 0 = 1 := h0
  have T1 : T 1 = (z 0 : ℂ) + z 1 := by
    have h := hrec 1 le_rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1] at h
    have h' : T 1 - ((z 0 : ℂ) + z 1) * T 0 = 0 := by
      simp [hT, sub_eq_add_neg] at h ⊢
      linear_combination h
    rw [T0] at h'
    linear_combination h'
  have Trec : ∀ j, T (j + 2) = ((z 0 : ℂ) + z 1) * T (j + 1) - (z 0 : ℂ) * z 1 * T j := by
    intro j
    have h := hrec (j + 2) (by omega)
    rw [show j + 2 + 1 = 3 + j by omega, Finset.sum_range_add] at h
    rw [Finset.sum_eq_zero (s := Finset.range j) (fun r _ => by
      rw [sum_powersetCard_big (fun i => (z i : ℂ)) (by omega)]; simp)] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2] at h
    have h' : T (j + 2) - ((z 0 : ℂ) + z 1) * T (j + 1) + (z 0 : ℂ) * z 1 * T j = 0 := by
      have a1 : j + 2 - 1 = j + 1 := by omega
      have a2 : j + 2 - 2 = j := by omega
      simp [hT, a1, a2, sub_eq_add_neg] at h ⊢
      linear_combination h
    linear_combination h'
  have key : ∀ n, T n = hs (z 0) (z 1) n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rw [T0, hs_zero]
    | one => rw [T1, hs_one]
    | more n ih1 ih2 => rw [Trec, hs_rec, ih1, ih2]
  rw [hrow, ← key n]

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem torus_element_eq_torus_power_mul_compact (a : Fˣ) : ∃ k ∈ integralGL F 2,
    (Ad3.dg2 a 1 : GL (Fin 2) F) = torusPow F 2 ![ord (a : F), 0] * k := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.LocalUnramified.exists_unit_eq_uniformizer_zpow_ord_mul F a
  refine ⟨integralGLHom F 2 (Ad3.dg2 u 1), ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul, coe_torusPow]
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg2, integralGLHom, Matrix.diagonal_mul, ← hu]

theorem spherical_whittaker_torus_formula {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (z : Fin 2 → ℂˣ) (a : Fˣ) :
    sphericalWhittaker ψ₀ z (Ad3.dg2 a 1) =
      if 0 ≤ ord (a : F) then sqrtQ F ^ (-ord (a : F)) * hs (z 0) (z 1) (ord (a : F)).toNat else 0 := by
  obtain ⟨k, hk, hdg⟩ := torus_element_eq_torus_power_mul_compact a
  rw [hdg, sphericalWhittaker_mul_right hψ₀ _ _ hk, sphericalWhittaker_torusPow hψ₀]
  by_cases h : 0 ≤ ord (a : F)
  · have hant : Antitone (![ord (a : F), 0] : Fin 2 → ℤ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    rw [if_pos hant, if_pos h, halfModulus_eq]
    have hr : rhoPair (![ord (a : F), 0] : Fin 2 → ℤ) = ord (a : F) := by
      simp [rhoPair, Fin.sum_univ_two]
    rw [hr, hn, evalAt_schur_row]
    simp
  · have hant : ¬ Antitone (![ord (a : F), 0] : Fin 2 → ℤ) := by
      intro hh
      have := hh (by decide : (0 : Fin 2) ≤ 1)
      simp at this
      exact h this
    rw [if_neg hant, if_neg h]

end Local

section Char

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unr_mul {χ₁ χ₂ : Fˣ →* ℂˣ} (h₁ : IsUnramifiedChar χ₁) (h₂ : IsUnramifiedChar χ₂) :
    IsUnramifiedChar (χ₁ * χ₂) := fun u hu => by
  have a := MonoidHom.mem_ker.1 (h₁ hu)
  have b := MonoidHom.mem_ker.1 (h₂ hu)
  simp [MonoidHom.mem_ker, a, b]

theorem unr_inv {χ : Fˣ →* ℂˣ} (h : IsUnramifiedChar χ) : IsUnramifiedChar χ⁻¹ := fun u hu => by
  have a := MonoidHom.mem_ker.1 (h hu)
  simp [MonoidHom.mem_ker, a]

theorem ofReal_pow_cpow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (u : ℂ) :
    (((r ^ n : ℝ)) : ℂ) ^ u = ((r : ℂ) ^ u) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hr, ih, pow_succ]

theorem mp_eq (a : Fˣ) {n : ℕ} (h : ord (a : F) = n) (u : ℂ) :
    Ad3.mp a u = ((residueCard F : ℂ) ^ (-u)) ^ n := by
  have hq : (0 : ℝ) < residueCard F := by
    exact_mod_cast (zero_lt_one.trans (one_lt_residueCard (K := F)))
  have hm : ((modulus (a : F) : NNReal) : ℝ) = ((residueCard F : ℝ)⁻¹) ^ n := by
    rw [GlobalTheory.CompanionTheory.LUGauge.modulus_coe, h, zpow_neg, zpow_natCast, inv_pow]
  rw [Ad3.mp, hm, ofReal_pow_cpow (by positivity)]
  congr 1
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by simp [Complex.natCast_arg, Real.pi_ne_zero.symm]),
    Complex.cpow_neg]
  simp

def gv (α β t : ℂ) (k : ℤ) : ℂ :=
  if 0 ≤ k then hs α β k.toNat * conj (hs α β k.toNat) * t ^ k.toNat else 0

theorem integrand_eq (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (z : Fin 2 → ℂˣ)
    {c : Fˣ →* ℂˣ} (hc : IsUnramifiedChar c) (s : ℂ) (a : Fˣ) :
    sphericalWhittaker ψ₀ z (Ad3.dg2 a 1) * conj (sphericalWhittaker ψ₀ z (Ad3.dg2 a 1)) *
        ((c a : ℂˣ) : ℂ) * Ad3.mp a (s - 1) =
      gv (z 0) (z 1) (((c (unifUnit F) : ℂˣ) : ℂ) * (residueCard F : ℂ) ^ (-s)) (ord (a : F)) := by
  rw [spherical_whittaker_torus_formula hψ₀, gv]
  by_cases h : 0 ≤ ord (a : F)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    have hq0 : (residueCard F : ℂ) ≠ 0 := by
      have : 0 < residueCard F := zero_lt_one.trans (one_lt_residueCard (K := F))
      exact_mod_cast this.ne'
    have hca : ((c a : ℂˣ) : ℂ) = ((c (unifUnit F) : ℂˣ) : ℂ) ^ n := by
      rw [quasiChar_apply_of_isUnramified hc a, hn, zpow_natCast, Units.val_pow_eq_pow_val]
    have hsq : conj (sqrtQ F) = sqrtQ F := by
      rw [sqrtQ, Complex.conj_ofReal]
    have hsq2 : sqrtQ F ^ 2 = (residueCard F : ℂ) := by
      rw [sqrtQ_sq]
      rfl
    have hsq0 : sqrtQ F ≠ 0 := sqrtQ_ne_zero
    have hcp : (residueCard F : ℂ) ^ (-(s - 1)) = (residueCard F : ℂ) ^ (-s) * (residueCard F : ℂ) := by
      rw [show -(s - 1) = -s + 1 by ring, Complex.cpow_add _ _ hq0, Complex.cpow_one]
    rw [if_pos h, if_pos h, hn, mp_eq a hn, hca, hcp]
    simp only [Int.toNat_natCast, map_mul, hsq, zpow_neg, zpow_natCast, map_inv₀, map_pow]
    have hone : (sqrtQ F ^ n)⁻¹ * (sqrtQ F ^ n)⁻¹ * (residueCard F : ℂ) ^ n = 1 := by
      rw [← hsq2, ← pow_mul, mul_comm 2 n, pow_mul, sq]
      field_simp
    rw [mul_pow, mul_pow]
    linear_combination (hs (z 0) (z 1) n * conj (hs (z 0) (z 1) n) * ((c (unifUnit F) : ℂˣ) : ℂ) ^ n *
      ((residueCard F : ℂ) ^ (-s)) ^ n) * hone
  · rw [if_neg h, if_neg h]
    simp

end Char

theorem euler_identity {α β t A : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (ht : ‖t‖ < 1)
    (hA : A = ∑' n : ℕ, gv α β t (n : ℤ)) :
    A * (1 - t ^ 2)⁻¹ = (1 - α * β⁻¹ * t)⁻¹ * (1 - t)⁻¹ * (1 - α⁻¹ * β * t)⁻¹ * (1 - t)⁻¹ := by
  have h0 : α ≠ 0 := by
    intro h
    simp [h] at hα
  have h1 : β ≠ 0 := by
    intro h
    simp [h] at hβ
  set x := (α * β)⁻¹ * t with hx
  have hxn : ‖x‖ < 1 := by
    simpa [hx, hα, hβ] using ht
  have hterm : ∀ n : ℕ, gv α β t (n : ℤ) = hs α β n ^ 2 * x ^ n := by
    intro n
    simp only [gv, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    rw [conj_hs hα hβ, hx, mul_pow]
    ring
  have hAe : A = ∑' n : ℕ, hs α β n ^ 2 * x ^ n := by
    rw [hA]
    exact tsum_congr hterm
  have key := (tsum_hs_sq hα hβ hxn).2
  rw [← hAe] at key
  have e1 : α * β * x = t := by
    rw [hx]
    field_simp
  have e2 : α ^ 2 * x = α * β⁻¹ * t := by
    rw [hx]
    field_simp
  have e3 : β ^ 2 * x = α⁻¹ * β * t := by
    rw [hx]
    field_simp
  rw [e1, e2, e3] at key
  have nz : ∀ w : ℂ, ‖w‖ = 1 → 1 - w * t ≠ 0 := by
    intro w hw h
    have : w * t = 1 := by linear_combination -h
    have h2 : ‖w * t‖ = 1 := by rw [this, norm_one]
    rw [norm_mul, hw, one_mul] at h2
    linarith
  have n1 : 1 - t ≠ 0 := by simpa using nz 1 norm_one
  have n2 : 1 - α * β⁻¹ * t ≠ 0 := nz _ (by simp [hα, hβ])
  have n3 : 1 - α⁻¹ * β * t ≠ 0 := nz _ (by simp [hα, hβ])
  have n4 : 1 + t ≠ 0 := by
    simpa [sub_eq_add_neg] using nz (-1) (by simp)
  have n5 : 1 - t ^ 2 ≠ 0 := by
    rw [show 1 - t ^ 2 = (1 - t) * (1 + t) by ring]
    exact mul_ne_zero n1 n4
  have hfin : A * ((1 - α * β⁻¹ * t) * (1 - t) * (1 - α⁻¹ * β * t) * (1 - t)) = 1 - t ^ 2 := by
    linear_combination (1 - t) * key
  rw [← mul_inv, ← mul_inv, ← mul_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  calc A * (1 - t ^ 2)⁻¹ * ((1 - α * β⁻¹ * t) * (1 - t) * (1 - α⁻¹ * β * t) * (1 - t))
      = (A * ((1 - α * β⁻¹ * t) * (1 - t) * (1 - α⁻¹ * β * t) * (1 - t))) * (1 - t ^ 2)⁻¹ := by ring
    _ = 1 := by rw [hfin, mul_inv_cancel₀ n5]

open Ad3 Ad3.R in

theorem rankinSelberg_unramified : Ad3.Loc2 → Ad3.R.E4 := by
  intro hL F _ _ _ _ _ _ ψ hψ μ₁ μ₂ c h1 h2 hc r1 r2 rc s hs' G hG
  have hψ₀ := GlobalTheory.CompanionTheory.LocalChar.sPsi F ψ hψ
  have hW := (hL F ψ hψ μ₁ μ₂ h1 h2).2 r1 r2
  set z : Fin 2 → ℂˣ := ![μ₁ (unifUnit F), μ₂ (unifUnit F)] with hz
  set α : ℂ := ((μ₁ (unifUnit F) : ℂˣ) : ℂ) with hα
  set β : ℂ := ((μ₂ (unifUnit F) : ℂˣ) : ℂ) with hβ
  set γ : ℂ := ((c (unifUnit F) : ℂˣ) : ℂ) with hγ
  set Q : ℂ := (residueCard F : ℂ) ^ (-s) with hQ
  set t : ℂ := γ * Q with ht
  have nα : ‖α‖ = 1 := h1.2 _
  have nβ : ‖β‖ = 1 := h2.2 _
  have nγ : ‖γ‖ = 1 := hc.2 _
  have hq1 : (1 : ℝ) < residueCard F := by exact_mod_cast (one_lt_residueCard (K := F))
  have hq0 : 0 < residueCard F := zero_lt_one.trans (one_lt_residueCard (K := F))
  have nQ : ‖Q‖ = (residueCard F : ℝ) ^ (-s.re) := by
    rw [hQ, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
  have nt : ‖t‖ = (residueCard F : ℝ) ^ (-s.re) := by
    rw [ht, norm_mul, nγ, one_mul, nQ]
  have nt1 : ‖t‖ < 1 := by
    rw [nt]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hGv : ∀ a : Fˣ, G a = gv α β t (ord (a : F)) := by
    intro a
    rw [hG a]
    have hind : (Ad3.R.ind0 : (Fin 2 → F) → ℂ) = Set.indicator {x | ∀ i, x i ∈ 𝒪[F]} 1 := rfl
    rw [hind, hW]
    exact integrand_eq _ hψ₀ z rc s a
  have hpow : ∀ n : ℕ, ord (((unifUnit F ^ n : Fˣ)) : F) = (n : ℤ) := by
    intro n
    have := ord_unifUnit_zpow (K := F) (n : ℤ)
    rwa [zpow_natCast] at this
  refine ⟨fun a u hu => ?_, fun a ha => ?_, ?_, fun n => ?_, ?_⟩
  · rw [hGv, hGv, ord_units_mul, hu, add_zero]
  · rw [hGv] at ha
    have h0 : 0 ≤ ord (a : F) := by
      by_contra h
      exact ha (by simp [gv, h])
    exact GlobalTheory.CompanionTheory.LUGauge.mem_integers_of_ord_nonneg a.ne_zero h0
  · rw [hGv]
    have : ord (((1 : Fˣ)) : F) = 0 := by simp [ord]
    rw [this]
    simp [gv, hs_zero]
  · rw [hGv, hpow]
    simp only [gv, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    have hb := norm_hs_le nα nβ n
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_pow, nt]
    have hpw : ((residueCard F : ℝ) ^ (-s.re)) ^ n = (residueCard F : ℝ) ^ (-((n : ℝ) * s.re)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [hpw, sq]
    gcongr
  · have hT : (∑' n : ℕ, G (unifUnit F ^ n)) = ∑' n : ℕ, gv α β t (n : ℤ) :=
      tsum_congr fun n => by rw [hGv, hpow]
    have hmain := euler_identity nα nβ nt1 hT
    have l1 : localLFactor (c * c) (2 * s) = (1 - t ^ 2)⁻¹ := by
      rw [localLFactor_of_isUnramified (unr_mul rc rc)]
      have : (residueCard F : ℂ) ^ (-(2 * s)) = Q ^ 2 := by
        rw [hQ, show -(2 * s) = ((2 : ℕ) : ℂ) * (-s) by push_cast; ring, Complex.cpow_nat_mul]
      rw [this, ht, mul_pow]
      simp [MonoidHom.mul_apply, sq, hγ]
    have l2 : localLFactor c s = (1 - t)⁻¹ := by
      rw [localLFactor_of_isUnramified rc]
    have l3 : localLFactor (μ₁ * μ₂⁻¹ * c) s = (1 - α * β⁻¹ * t)⁻¹ := by
      rw [localLFactor_of_isUnramified (unr_mul (unr_mul r1 (unr_inv r2)) rc), ht, hQ]
      simp [MonoidHom.mul_apply, hα, hβ, hγ, mul_assoc]
    have l4 : localLFactor ((μ₁ * μ₂⁻¹)⁻¹ * c) s = (1 - α⁻¹ * β * t)⁻¹ := by
      have v : ((((μ₁ * μ₂⁻¹)⁻¹ * c) (unifUnit F) : ℂˣ) : ℂ) = α⁻¹ * β * γ := by
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv, Units.val_mul,
          Units.val_inv_eq_inv_val]
        ring
      rw [localLFactor_of_isUnramified (unr_mul (unr_inv (unr_mul r1 (unr_inv r2))) rc), v, ht, mul_assoc (α⁻¹ * β)]
    rw [l1, lf3, l2, l3, l4]
    exact hmain

end GlobalTheory.CompanionTheory.RSUnram

end
