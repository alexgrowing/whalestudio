import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PsiBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem neg_val {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (χ : Γ →* Oˣ) (h0 : 0 < orderOf χ)
    (h : Even (orderOf χ)) : ∃ σ, χ σ = -1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : χ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  obtain ⟨σ, hσ⟩ : ∃ σ, χ σ ^ k ≠ 1 := by
    by_contra hn
    push Not at hn
    exact h1 (MonoidHom.ext hn)
  have h2 : (χ σ ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_two, ← hk, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
  have h3 : ((χ σ ^ k : Oˣ) : O) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  refine ⟨σ ^ k, ?_⟩
  rw [map_pow]
  rcases sq_eq_one_iff.1 h3 with h4 | h4
  · exact absurd (Units.ext h4) hσ
  · exact Units.ext h4

theorem UpperTheory.V.Ws.ev2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∃ t, D.om t = 1 ∧ κ t = 1 ∧ Raw.bar D.Psi t = -1 := by
  intro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, _, _, _, _, ⟨_, hev, _⟩, hO⟩ κ j hκ
  have lp : l.Prime := hl.out
  have hT : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    have := hG.om_bar σ
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 this⟩
  have hk := ((omT Ω l c).2 D.om hT).2.1
  obtain ⟨b, -, -, hb⟩ := (psiBar Ω l c D.om hT h.N ψ).1
  have ho := (psiBar Ω l c D.om hT h.N (chiP l ψ)).2.2.1
  obtain ⟨σ, hσ⟩ := neg_val (Chr.dirG ℚ Ω (chiP l ψ)) (ho ▸ (chiP l ψ).orderOf_pos) (ho ▸ hev)
  obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O h.N l lp
  have h1 : comp l (chiP l ψ) = 1 := by rw [chiP, hmul, hinv, (h6 _).1, mul_inv_cancel]
  have hA := hG.pl_over l lp
  have hI := ((compIne Ω h.N l lp _ hA).2 c.O (chiP l ψ)).2.2 h1
  obtain ⟨τ, hτ, hc⟩ : Chr.cls ℚ Ω l σ ∈ (Ine (F := ℚ) (D.pl l)).map (Chr.cls ℚ Ω l) := by
    rw [(compIne Ω l l lp _ hA).1, (projFacts l l lp).2.2.2.2.2.1, MonoidHom.mem_ker]
    have : Subsingleton (ZMod (ordCompl[l] l)) := by
      rw [lp.factorization_self, pow_one, Nat.div_self lp.pos]
      infer_instance
    exact Subsingleton.elim _ _
  have e1 : D.om (σ * τ⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hk, MonoidHom.mem_ker, map_mul, map_inv, hc, mul_inv_cancel]
  have e2 : Chr.dirG ℚ Ω (chiP l ψ) (σ * τ⁻¹) = -1 := by
    rw [map_mul, map_inv, hσ, MonoidHom.mem_ker.1 (hI hτ), inv_one, mul_one]
  have e3 : D.om ((σ * τ⁻¹) ^ l ^ j) = 1 := by rw [map_pow, e1, one_pow]
  have e4 : Chr.dirG ℚ Ω (chiP l ψ) ((σ * τ⁻¹) ^ l ^ j) = -1 := by
    rw [map_pow, e2, ((lp.odd_of_ne_two hG.l_odd).pow).neg_one_pow]
  refine ⟨(σ * τ⁻¹) ^ l ^ j, e3, ?_, ?_⟩
  · rw [map_pow, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply]
  · have e5 := hb D.e ((σ * τ⁻¹) ^ l ^ j)
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, e3, e4, one_pow, one_mul, ← hO.psi,
      ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at e5
    refine e5.trans ?_
    simp
