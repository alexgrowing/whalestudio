import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOneAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem invN_le {n : ℕ} {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) :
    invN u ≤ invN (swap a c * u) + 1 := by
  have hac : a ≠ c := fun e => by rw [e] at h; omega
  obtain ⟨hA, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  rcases lt_trichotomy (u⁻¹ a) (u⁻¹ c) with hl | he | hl
  · have := (hA a c h u hl).2.2
    omega
  · exact absurd (u⁻¹.injective he) hac
  · have hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c := by
      rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]
      exact hl
    have := (hA a c h _ hw').2.2
    rw [swap_mul_self_mul] at this
    omega

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  obtain ⟨hA, -, h1, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have hlt : (1 : Perm (Fin n))⁻¹ a < (1 : Perm (Fin n))⁻¹ c := by
    simp only [inv_one, Perm.one_apply, Fin.lt_def]
    omega
  have e := (hA a c h 1 hlt).2.2
  rw [mul_one, show invN (1 : Perm (Fin n)) = 0 by rw [invN, h1, Finset.card_empty], zero_add] at e
  rw [(UpperTheory.V.AlgebraTools.hkOne R n q H b).1, e, pow_one]

private theorem step {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H]
    (b : Bern n q H) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsFractionRing (MvPolynomial (Fin n) R) K] {a c : Fin n} (h : a.val + 1 = c.val)
    (y : MvPolynomial (Fin n) R) :
    ∃ y' : MvPolynomial (Fin n) R, b.T (swap a c) * b.th y * b.one = b.th y' * b.one ∧
      algebraMap _ K y' =
        algebraMap (MvPolynomial (Fin n) R) K (X a - C q * X c) / algebraMap (MvPolynomial (Fin n) R) K (X a - X c) *
            algebraMap _ K (rename (swap a c) y) +
          algebraMap (MvPolynomial (Fin n) R) K ((C q - 1) * X a) /
            algebraMap (MvPolynomial (Fin n) R) K (X a - X c) * algebraMap _ K y := by
  have hac : a ≠ c := fun e => by rw [e] at h; omega
  obtain ⟨z, hz, hT⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y
  refine ⟨C q * rename (swap a c) y + (C q - 1) * (X a * z), ?_, ?_⟩
  · have e1 : (C q * rename (swap a c) y + (C q - 1) * (X a * z) : MvPolynomial (Fin n) R) =
        q • rename (swap a c) y + (q - 1) • (X a * z) := by
      rw [smul_eq_C_mul, smul_eq_C_mul, map_sub, map_one]
    rw [hT, e1, map_add, map_smul, map_smul, add_mul, add_mul, mul_assoc, swap_one b h, mul_smul_comm,
      smul_mul_assoc q]
  · have hne : algebraMap (MvPolynomial (Fin n) R) K (X a - X c) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K), sub_eq_zero]
      exact fun e => hac (X_injective e)
    have hz' := congrArg (algebraMap (MvPolynomial (Fin n) R) K) hz
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hne]
    simp only [map_add, map_mul, map_sub, map_one] at hz' ⊢
    linear_combination (algebraMap (MvPolynomial (Fin n) R) K (C q) - 1) *
      algebraMap (MvPolynomial (Fin n) R) K (X a) * hz'

theorem UpperTheory.V.AlgebraTools.hkAct :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (w : Perm (Fin n)),
      ∃ f : Perm (Fin n) → K,
        (∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, b.T w * b.th x * b.one = b.th y * b.one ∧
          algebraMap _ K y = ∑ u, f u * algebraMap _ K (rename u x)) ∧
        f w = ∏ p ∈ invSet w, algebraMap (MvPolynomial (Fin n) R) K (X p.1 - C q * X p.2) / algebraMap (MvPolynomial (Fin n) R) K (X p.1 - X p.2) ∧
        ∀ u, u ≠ w → invN w ≤ invN u → f u = 0 := by
  intro R _ _ n q H _ _ b K _ _ _
  obtain ⟨hA, -, h1, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
  · refine ⟨fun u => if u = 1 then 1 else 0, fun x => ⟨x, by rw [b.T_one, one_mul], ?_⟩, ?_, ?_⟩
    · simp [ite_mul]
    · simp [h1]
    · intro u hu _
      simp [hu]
  · rintro a c h w hw ⟨f, hf, hfw, hf0⟩
    obtain ⟨hS, hnm, hN⟩ := hA a c h w hw
    let σ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (renameEquiv R (swap a c)).toRingEquiv
    have hσ : ∀ x : MvPolynomial (Fin n) R,
        σ (algebraMap _ K x) = algebraMap _ K (rename (swap a c) x) := fun x =>
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
    refine ⟨fun u =>
      algebraMap (MvPolynomial (Fin n) R) K (X a - C q * X c) / algebraMap (MvPolynomial (Fin n) R) K (X a - X c) *
          σ (f (swap a c * u)) +
        algebraMap (MvPolynomial (Fin n) R) K ((C q - 1) * X a) /
          algebraMap (MvPolynomial (Fin n) R) K (X a - X c) * f u, fun x => ?_, ?_, ?_⟩
    · obtain ⟨y, hy, hyK⟩ := hf x
      obtain ⟨y', hy', hyK'⟩ := step b K h y
      refine ⟨y', ?_, ?_⟩
      · rw [b.T_mul a c h w hw, mul_assoc (b.T _), mul_assoc (b.T _), hy, ← mul_assoc, hy']
      · rw [hyK', ← hσ, hyK, map_sum, Finset.mul_sum, Finset.mul_sum]
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
        congr 1
        refine Fintype.sum_equiv (Equiv.mulLeft (swap a c)) _ _ fun u => ?_
        rw [Equiv.coe_mulLeft, swap_mul_self_mul, map_mul, hσ, rename_rename, Perm.coe_mul]
    · have h0 : f (swap a c * w) = 0 := hf0 _ (fun e => by rw [e] at hN; omega) (by omega)
      beta_reduce
      rw [h0, mul_zero, add_zero, swap_mul_self_mul, hS, Finset.prod_insert hnm, Finset.prod_image, hfw, map_prod]
      · congr 1
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [map_div₀, hσ, hσ]
        simp only [map_sub, map_mul, rename_X, rename_C]
      · rintro ⟨u, v⟩ - ⟨u', v'⟩ - e
        obtain ⟨e1, e2⟩ := Prod.mk.inj e
        exact Prod.ext ((swap a c).injective e1) ((swap a c).injective e2)
    · intro u hu hle
      have hle' := invN_le h u
      have h0 : f u = 0 := hf0 _ (fun e => by rw [e] at hle; omega) (by omega)
      have h0' : f (swap a c * u) = 0 :=
        hf0 _ (fun e => hu (by rw [← e, swap_mul_self_mul])) (by omega)
      beta_reduce
      rw [h0, h0', map_zero, mul_zero, mul_zero, add_zero]
