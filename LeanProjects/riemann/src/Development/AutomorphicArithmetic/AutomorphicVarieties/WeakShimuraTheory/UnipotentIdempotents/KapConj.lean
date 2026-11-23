import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kapConj_alg {M : Type} [CommGroup M] (k k' y b b' o x p E : M) (e n : ℕ)
    (h0 : k * k' * (o ^ (e + 3) * x * p) = 1) (h1 : y ^ 2 * o = E) (h2 : b * b' = 1) :
    (k * y⁻¹ ^ (e + 4) * b ^ n) * (k' * y⁻¹ ^ (e + 4) * b' ^ n) * (E * o⁻¹ * x * (E ^ e * p)) * E ^ 3 = 1 := by
  subst h1
  apply Additive.ofMul.injective
  have h0' := congrArg Additive.ofMul h0
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, add_smul, one_smul, neg_smul, smul_add, smul_neg] at h0' h2' ⊢
  have hk : Additive.ofMul k' = -(Additive.ofMul k +
      (e • Additive.ofMul o + 3 • Additive.ofMul o + Additive.ofMul x + Additive.ofMul p)) := by
    rw [eq_neg_iff_add_eq_zero, ← h0']
    abel
  have hb : Additive.ofMul b' = -Additive.ofMul b := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2'
  rw [hk, hb]
  simp only [smul_add, smul_neg, neg_add, neg_neg, two_smul]
  abel

theorem UpperTheory.V.Ws.Lk.kapConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), T.Deep → ∀ σ ∉ T.K.fixingSubgroup, ∀ g g' : G T.L Ω, resQ T.L g' = σ * resQ T.L g * σ⁻¹ → P.κ g * P.κ g' * toQ D.th (resQ T.L g) * cycBar T.L Ω l g ^ 3 = 1 ∧ P.βL g * P.βL g' = 1 ∧ P.tL g * P.tL g' = 1 := by
  intro Ω _ _ _ l _ c D T P hDeep σ hσ g g' hgg
  have hKL := K_le T
  have hFL : T.F ≤ T.L := T.hL ▸ le_sup_left
  have hres : ∀ h : G T.L Ω, resQ T.K (resLe hKL h) = resQ T.L h := fun h => rfl
  have hresF : ∀ h : G T.L Ω, resQ T.F (resLe hFL h) = resQ T.L h := fun h => rfl
  have hss : resQ T.K (resLe hKL g') = σ * resQ T.K (resLe hKL g) * σ⁻¹ := by
    rw [hres, hres]
    exact hgg
  obtain ⟨m, hm, hψ⟩ := hDeep
  have hψg : ∃ m, l.Coprime m ∧ D.ψ (resQ T.K (resLe hKL g)) ^ m = 1 :=
    ⟨m, hm, by rw [hres, ← hresF]; exact hψ _⟩
  have h0 := P.κ₀_conj σ hσ _ _ hss hψg
  obtain ⟨hb, ht⟩ := P.conj σ hσ _ _ hss
  refine ⟨?_, hb, ht⟩
  have hγ : P.γ (resQ T.L g') = P.γ (resQ T.L g) := by
    rw [hgg, map_mul, map_mul, map_inv, mul_comm (P.γ σ), mul_inv_cancel_right]
  have hcyc : cycBar T.L Ω l g = cycBar ℚ Ω l (resQ T.L g) := by
    rfl
  have hchi : ∀ x, toQ (chiO ℚ Ω l c.O) x = cycBar ℚ Ω l x := fun x => by
    rw [← (auChi ℚ Ω c).1]
  have hth : ∀ x, toQ D.th x = toQ (chiO ℚ Ω l c.O) x * (toQ D.om x)⁻¹ * toQ D.ξ x *
      (toQ (chiO ℚ Ω l c.O) x ^ D.e * toQ D.ψ x) := by
    intro x
    simp only [toQ, W.pushCh, Raw.th, Raw.al, Raw.Psi, Chr.Psi, MonoidHom.comp_apply, MonoidHom.mul_apply,
      MonoidHom.inv_apply, map_mul, map_inv]
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) x = (chiO ℚ Ω l c.O x) ^ (D.e : ℤ) from rfl, zpow_natCast, map_pow]
  have hk0 : toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) (resQ T.L g) =
      toQ D.om (resQ T.L g) ^ (D.e + 3) * toQ D.ξ (resQ T.L g) * toQ D.ψ (resQ T.L g) := by
    simp only [toQ, W.pushCh, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow]
  rw [hres, hk0] at h0
  have h1 := P.γ_sq (resQ T.L g)
  have key := kapConj_alg _ _ _ _ _ _ _ _ _ D.e (D.e % 2) h0 h1 hb
  rw [hth, hchi, hcyc]
  simp only [Pre.κ, Pre.βL, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, MonoidHom.inv_apply]
  rw [hγ]
  exact key
