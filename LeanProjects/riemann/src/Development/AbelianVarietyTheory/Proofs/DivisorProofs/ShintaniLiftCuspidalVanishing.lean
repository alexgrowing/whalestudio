import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldFrobeniusPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRootPowerSumMapGaloisEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSumEqCharSumAgainstCuspForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_cusp_kills_of_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hnd hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite F'
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
  set K := k * ∑ i ∈ Finset.range l, q ^ (n * i) with hK_def
  obtain ⟨hregK, a, ha⟩ := GlobalTheory.T.regular_pair_lift_to_prime_power_field q l n k hq2 hl hn hnd hreg
  have hregK' : Reg (Nat.card F') n K := by rw [hcard']; exact hregK
  obtain ⟨hYchar, -⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F' θ hθ n K hn hregK'
  have hYs : ∀ g, cusp θ n K (galAct F F' n s g) = cusp θ n K g := by
    intro g
    obtain ⟨⟨i, hi⟩, hi'⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 s
    simp only at hi'
    obtain ⟨r, hp, hr⟩ := FiniteField.card F (ringChar F)
    have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
    have hsx : ∀ x, s.toRingEquiv x = x ^ (ringChar F' ^ ((r : ℕ) * i)) := by
      intro x
      change s x = _
      rw [← hi', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hr, hchar, pow_mul]
    have h1 := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ s.toRingEquiv ((r : ℕ) * i) hsx n K g
    have hpq : ringChar F' ^ ((r : ℕ) * i) = q ^ i := by
      rw [hchar, pow_mul, ← hr, hq_def, Nat.card_eq_fintype_card]
    rw [hpq] at h1
    have hpow : ∀ j, K * q ^ j ≡ K * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
      intro j
      induction j with
      | zero => simp only [pow_zero, mul_zero, mul_one]; exact Nat.ModEq.refl _
      | succ j ih =>
        have e1 : K * q ^ (j + 1) = (K * q ^ j) * q := by ring
        have e2 : K * Nat.card F' ^ (a * (j + 1)) = (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) := by
          rw [hcard']; ring
        rw [e1, e2]
        calc K * q ^ j * q ≡ K * Nat.card F' ^ (a * j) * q [MOD Nat.card F' ^ n - 1] := ih.mul_right _
          _ = (K * q) * Nat.card F' ^ (a * j) := by ring
          _ ≡ (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
            apply Nat.ModEq.mul_right
            rw [hcard']; exact ha
    have h2 := GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq F' θ hθ n K (K * q ^ i) (a * i) hn (hpow i)
    rw [galAct_apply]
    exact h1.trans (congrFun h2 g)
  obtain ⟨X0, hX0, hX0a, hX0b⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc_def
  have hc2 : c * c = 1 := by rw [hc_def, ← mul_pow]; simp
  have hcstar : star c = c := by rw [hc_def]; simp
  set X : GHat F F' n → ℂ := fun x => c * X0 x with hX_def
  have hX : X ∈ Virt ℂ ℂ (GHat F F' n) := by
    have e : X = ((-1 : ℤ) ^ (n - 1)) • X0 := by
      funext x
      simp only [hX_def, Pi.smul_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hc_def]
    rw [e]
    exact AddSubgroup.zsmul_mem _ hX0 _
  have hfun : (fun δ => X (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := by
    funext δ
    simp only [hX_def, hX0b]
    by_cases h : ∃ γ, IsNorm s δ γ <;> simp [shLift, cusp, h, hc_def]
  have hcl : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    have := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y
    simp only [cusp]
    rw [this]
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy h
    apply hinj
    refine hθ _ _ ?_ ?_ h
    · exact fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    · exact fun h0 => hy (hinj (h0.trans (map_zero ι).symm))
  obtain ⟨-, hnormF⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hΓ : Nat.card (F' ≃ₐ[F] F') = l := IsGalois.card_aut_eq_finrank F F'
  have htop : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := fun t => by
    rw [zpowers_eq_top_of_prime_card hΓ hs]; trivial
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s htop n _ _ hcl hcl
  rw [hnormF] at hiso
  have hnorm : ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    have e : ∀ g, X (inl g * inr s) * star (X (inl g * inr s)) =
        shLift s (cusp (pullθ ι θ) n k) g * star (shLift s (cusp (pullθ ι θ) n k) g) := fun g => by
      rw [← congrFun hfun g]
    rw [finsum_congr e]
    have hpos : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    apply mul_left_cancel₀ hpos
    rw [hiso, mul_comm]
  set S : F'[X] → ℂ := fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) with hS_def
  have hS1 : S 1 = 0 := by
    simp only [hS_def, Polynomial.map_one]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [rootSum]
  have hSprod : S = fun P => ∏ j : Fin l, rootSum θ (k * q ^ (j : ℕ)) P := by
    funext P
    simp only [hS_def]
    rw [GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k P, Fin.prod_univ_eq_prod_range (fun j => rootSum θ (k * q ^ j) P) l]
  have hprim := GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form F' θ S n K hS1
  have hprod := GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum F' θ hθ n K l (fun j => k * q ^ (j : ℕ)) hn
  rw [hcard'] at hprod
  set cnt := (Finset.univ.filter fun a : Fin l → Fin n =>
    K ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ n - 1]).card with hcnt_def
  have hcnt : cnt ≡ 1 [MOD l] := GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd q l n k hq2 hl hn hnd hreg
  have hz : ∑ᶠ g, X (inl g) * star (cusp θ n K g) = ((cnt : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [finsum_eq_sum_of_fintype] at hprim hprod ⊢
    have e1 : ∀ g, X (inl g) * star (cusp θ n K g) = c * (psiG S n g * star (cusp θ n K g)) := fun g => by
      simp only [hX_def, hX0a]; ring
    rw [Finset.sum_congr rfl (fun g _ => e1 g), ← Finset.mul_sum, hprim]
    have e2 : ∀ g, chG S n g * star (cusp θ n K g) = star (cusp θ n K g * star (chG S n g)) := fun g => by
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun g _ => e2 g), ← star_sum]
    have e3 : ∀ g, cusp θ n K g * star (chG S n g) = c * (psiG (rootSum θ K) n g * star (chG S n g)) :=
      fun g => by simp only [cusp, hc_def]; ring
    rw [Finset.sum_congr rfl (fun g _ => e3 g), ← Finset.mul_sum, hSprod, hprod, star_mul', hcstar, ← mul_assoc, hc2,
      one_mul, star_mul', star_natCast, star_natCast]
    push_cast
    ring
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (cnt : ℤ)) := by
    rw [hΓ, Int.natCast_dvd_natCast]
    intro h
    have h1 : cnt % l = 1 % l := hcnt
    rw [(Nat.dvd_iff_mod_eq_zero).1 h, Nat.mod_eq_of_lt hl.one_lt] at h1
    exact zero_ne_one h1
  have key := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X hX hnorm (cusp θ n K)
    hYchar hYs (cnt : ℤ) hz hndvd
  rw [hfun] at key
  exact key

end GlobalTheory.Shin
