import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasProdMoebiusConvOfNormLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardDivisorsSqLeTwoMulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSquareCoefficientLeDivisorBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumSquareCoefficientLocalSeriesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableTwistedSquareCoefficientsStatement

open Ad3 Ad3.S
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped LSeries.notation

noncomputable section

namespace GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients

theorem unr_mul (v : Pl) {μ₁ μ₂ : (Qv v)ˣ →* ℂˣ} (h1 : IsUnramifiedChar μ₁) (h2 : IsUnramifiedChar μ₂) :
    IsUnramifiedChar (μ₁ * μ₂) := by
  intro u hu
  have a1 := h1 hu
  have a2 := h2 hu
  simp only [MonoidHom.mem_ker, MonoidHom.mul_apply] at a1 a2 ⊢
  rw [a1, a2, mul_one]

theorem unr_inv (v : Pl) {μ : (Qv v)ˣ →* ℂˣ} (h : IsUnramifiedChar μ) : IsUnramifiedChar μ⁻¹ := by
  intro u hu
  have a1 := h hu
  simp only [MonoidHom.mem_ker, MonoidHom.inv_apply] at a1 ⊢
  rw [a1, inv_one]

theorem e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2 := by
  intro h1b h2a h2b N M _ _ hM χ D a ha hsat c δ T hadm hT c' hc' s hs
  obtain ⟨⟨e, he⟩, hL⟩ := h1b
  have hk : 1 ≤ D.k := le_trans (by norm_num) D.three
  set ψ : DirichletCharacter ℂ M := DirichletCharacter.changeLevel hM χ⁻¹ with hψ
  set Nf : ℕ → ℂ := fun n => ψ (n : ZMod M) * a (n ^ 2) with hNf
  have hpure : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧
      α * β = χ p * (p : ℂ) ^ (D.k - 1) ∧ ‖α‖ = ‖β‖ := by
    intro p hp hpN
    obtain ⟨q, hq⟩ : ∃ q : Nat.Primes, (q : ℕ) = p := ⟨⟨p, hp⟩, rfl⟩
    set v : Pl := e.symm q with hvdef
    have hv : pOf v = p := by rw [← he v, hvdef, Equiv.apply_symm_apply, hq]
    have hvb : v ∉ D.bad := by rw [hsat.1, hv]; exact hpN
    obtain ⟨α, β, h1, h2, h3⟩ := hsat.2 _ hvb
    refine ⟨α, β, by rw [← hv]; exact h1, by rw [← hv]; exact h2, ?_⟩
    have hu := (D.unit v).2 (unifUnit (Qv v))
    rw [h3, Units.val_div_eq_div_val, norm_div] at hu
    have hβ : ‖(β : ℂ)‖ ≠ 0 := by simp
    field_simp at hu
    exact hu
  have hb : ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (D.k - 1) := by
    intro n hn
    refine (GlobalTheory.T.norm_square_coefficient_le_divisor_bound D.k N χ a ha h2a hpure n hn).trans ?_
    exact mul_le_mul_of_nonneg_right (GlobalTheory.T.card_divisors_sq_le_two_mul' n) (by positivity)
  have hsumm : LSeriesSummable Nf (s + D.k - 1) := GlobalTheory.T.summable_twisted_square_coefficients M N D.k hM χ a hk hb s hs
  have hN1 : Nf 1 = 1 := by simp [Nf, ha.2.1]
  have hNmul : ∀ {m n : ℕ}, m.Coprime n → Nf (m * n) = Nf m * Nf n := by
    intro m n h
    simp only [Nf, Nat.cast_mul, map_mul, mul_pow]
    rw [(h2a D.k N χ a ha).1 _ _ (Nat.Coprime.pow 2 2 h)]
    ring
  have hA := GlobalTheory.CompanionTheory.SquareEuler.hasProd_twist c' hN1 hNmul hsumm
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hB := DirichletCharacter.LSeries_eulerProduct_hasProd (c' ^ 2) h2s
  have hP := hB.mul hA
  have hfac : ∀ v : Pl, (fun p : Nat.Primes => (1 - (c' ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ *
      ∑' j : ℕ, Nf ((p : ℕ) ^ j) * (c' ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(s + D.k - 1))) ^ j) (e v) =
      Set.mulIndicator {v | v ∉ T} (fun v => lf3 (D.ν v) (localChar c v) s) v := by
    intro v
    dsimp only
    have hp : (pOf v).Prime := by rw [← he v]; exact (e v).2
    rw [he v]
    have hp0 : ((pOf v : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    by_cases hvT : v ∈ T
    · have hpM : pOf v ∣ M := (hT v).1 hvT
      have hnu : ¬ IsUnit ((pOf v : ℕ) : ZMod M) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpM)
      have hc0 : c' ((pOf v : ℕ) : ZMod M) = 0 := MulChar.map_nonunit _ hnu
      have hc20 : (c' ^ 2) ((pOf v : ℕ) : ZMod M) = 0 := MulChar.map_nonunit _ hnu
      rw [Set.mulIndicator_of_notMem (by simpa using hvT), hc20, hc0]
      simp only [zero_mul, sub_zero, inv_one, one_mul]
      rw [tsum_eq_single 0]
      · simp [hN1]
      · intro j hj
        simp [hj]
    · rw [Set.mulIndicator_of_mem (by simpa using hvT)]
      have hvb : v ∉ D.bad := fun h => hvT (hadm.bad h)
      obtain ⟨α, β, hsum, hprod, hν⟩ := hsat.2 v hvb
      have hpM : ¬ pOf v ∣ M := fun h => hvT ((hT v).2 h)
      have hcp := hc' v hpM
      have hunit : IsUnit ((pOf v : ℕ) : ZMod M) :=
        (ZMod.isUnit_iff_coprime _ _).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have hψp : ψ ((pOf v : ℕ) : ZMod M) = (χ (pOf v))⁻¹ := by
        have h0 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ⁻¹ hM hunit.unit
        rw [IsUnit.unit_spec] at h0
        rw [hψ, h0, ZMod.cast_natCast hM, MulChar.inv_apply_eq_inv']
      have hNfp : ∀ j, Nf (pOf v ^ j) = (χ (pOf v))⁻¹ ^ j * a (pOf v ^ (2 * j)) := by
        intro j
        simp only [Nf, Nat.cast_pow, map_pow, hψp]
        rw [← pow_mul, mul_comm j 2]
      have hu1 := D.unr v hvb
      have hu2 := hadm.unr v hvT
      have hα : (α : ℂ) ≠ 0 := α.ne_zero
      have hβ : (β : ℂ) ≠ 0 := β.ne_zero
      have hν' : ((D.ν v (unifUnit (Qv v)) : ℂˣ) : ℂ) = (α : ℂ) / β := by rw [hν, Units.val_div_eq_div_val]
      have hr : ‖(α : ℂ) / β‖ = 1 := by rw [← hν']; exact (D.unit v).2 _
      have hloc := GlobalTheory.T.hasSum_square_coefficient_local_series h2a h2b D.k N χ a ha hk (pOf v) hp α β (c' ((pOf v : ℕ) : ZMod M)) s hα hβ hsum hprod hr
        (DirichletCharacter.norm_le_one _ _) (by linarith)
      rw [tsum_congr (fun j => by rw [hNfp j]), hloc.tsum_eq]
      rw [lf3, hL v _ (unr_mul v hu1 hu2), hL v _ hu2, hL v _ (unr_mul v (unr_inv v hu1) hu2)]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hν', ← hcp]
      have hX2 : (c' ^ 2) ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-(2 * s)) =
          (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 := by
        rw [show -(2 * s) = -s + -s by ring, Complex.cpow_add _ _ hp0, MulChar.pow_apply' _ two_ne_zero]
        ring
      have hXn := GlobalTheory.CompanionTheory.SquareEuler.norm_X_lt_one c' (s := s) (by linarith) hp
      have h1X2 : 1 - (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
        intro h
        have h' : ‖c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)‖ ^ 2 = 1 := by
          rw [← norm_pow, show (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 = 1 by
            linear_combination -h, norm_one]
        nlinarith [norm_nonneg (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s))]
      rw [hX2, ← mul_assoc, inv_mul_cancel₀ h1X2, one_mul]
      ring
  have hP2 : HasProd (Set.mulIndicator {v | v ∉ T} (fun v => lf3 (D.ν v) (localChar c v) s))
      (L ↗(c' ^ 2) (2 * s) * L (↗c' * Nf) (s + D.k - 1)) := by
    have := (e.hasProd_iff).2 hP
    convert this using 1
    funext v
    exact (hfac v).symm
  rw [← hasProd_subtype_iff_mulIndicator] at hP2
  have hfun : (fun n : ℕ => (c' * DirichletCharacter.changeLevel hM χ⁻¹) (n : ZMod M) * a (n ^ 2)) =
      ↗c' * Nf := by
    funext n
    simp only [Pi.mul_apply, Nf, hψ, MulChar.coeToFun_mul]
    ring
  rw [DirichletCharacter.LFunction_eq_LSeries _ h2s, hfun]
  exact hP2.tprod_eq

end GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients
