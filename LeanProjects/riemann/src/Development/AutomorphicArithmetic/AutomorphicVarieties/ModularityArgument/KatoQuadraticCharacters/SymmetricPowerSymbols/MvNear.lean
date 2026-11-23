import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem semi_aeval {K L : Type} [Field K] [Field L] [Algebra K L] (σ : RingAut L) (τ : K ≃+* K)
    (hσ : ∀ f, σ (algebraMap K L f) = algebraMap K L (τ f)) (p : Polynomial K) (hp : ∀ c ∈ p.coeffs, τ c = c) (x : L) :
    σ (Polynomial.aeval x p) = Polynomial.aeval (σ x) p := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, hσ]
  by_cases h : p.coeff i = 0
  · simp [h]
  · rw [hp _ (Polynomial.coeff_mem_coeffs h)]

private theorem fix_lift {K : Type} [Field K] [CharZero K] (B : Finset (AlgebraicClosure K)) :
    ∃ S : Finset K, ∀ (τ : K ≃+* K) (σ₀ : RingAut (AlgebraicClosure K)),
      (∀ f, σ₀ (algebraMap K _ f) = algebraMap K _ (τ f)) → (∀ f ∈ S, τ f = f) →
      ∃ σ : RingAut (AlgebraicClosure K), (∀ f, σ (algebraMap K _ f) = algebraMap K _ (τ f)) ∧ ∀ b ∈ B, σ b = b := by
  classical
  set E := IntermediateField.adjoin K (B : Set (AlgebraicClosure K)) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  have hβ : IntermediateField.adjoin K {(α : AlgebraicClosure K)} = E := by
    have := congrArg (IntermediateField.map E.val) hα
    rw [IntermediateField.adjoin_map] at this
    simpa [← AlgHom.fieldRange_eq_map] using this
  generalize (α : AlgebraicClosure K) = β at hβ
  have hi : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hp : ∀ b : AlgebraicClosure K, ∃ p : Polynomial K, b ∈ B → Polynomial.aeval β p = b := by
    intro b
    by_cases hb : b ∈ B
    · have h1 : b ∈ IntermediateField.adjoin K {β} := by
        rw [hβ]; exact IntermediateField.subset_adjoin _ _ hb
      have h2 : b ∈ (IntermediateField.adjoin K {β}).toSubalgebra := h1
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval] at h2
      obtain ⟨p, hp⟩ := h2
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose p hp using hp
  refine ⟨(minpoly K β).coeffs ∪ B.biUnion fun b => (p b).coeffs, fun τ σ₀ h0 hS => ?_⟩
  have hr : Polynomial.aeval (σ₀ β) (minpoly K β) = 0 := by
    rw [← semi_aeval σ₀ τ h0 _ fun c hc => hS c (Finset.mem_union_left _ hc), minpoly.aeval, map_zero]
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root hi.isAlgebraic hr
  have hl : ∀ f, (σ₀.trans g.toRingEquiv) (algebraMap K _ f) = algebraMap K _ (τ f) := fun f => by
    rw [RingEquiv.trans_apply, h0]; exact g.commutes _
  refine ⟨σ₀.trans g.toRingEquiv, hl, fun b hb => ?_⟩
  have := semi_aeval _ τ hl (p b) (fun c hc => hS c (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hb, hc⟩))) β
  rw [hp b hb] at this
  rw [this]
  have e : (σ₀.trans g.toRingEquiv) β = β := hg
  rw [e, hp b hb]

theorem UpperTheory.V.Z.Kato.Sym.mvNear :
    UpperTheory.V.Z.Kato.Sym.MvNear := by
  classical
  intro Ω _ _ _ ε X m hm u v P hP
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  obtain ⟨hz, -, l3, -, -, l6, -⟩ := lgB Ω ε X m hm
  obtain ⟨B, hB⟩ := hP.lc
  obtain ⟨S, hS⟩ := fix_lift (K := X.K) ({P.a, P.b, zt X m} ∪ B.biUnion fun b => ((minpoly X.K b).aroots (Kb X)).toFinset)
  refine ⟨S, fun τ s hτ hfix => ?_⟩
  obtain ⟨σ₀, h0⟩ := (admB Ω ε X).2.2.2.2.2.2.1 τ
  obtain ⟨σ, hσ, hb⟩ := hS τ σ₀ h0 hfix
  have ea : σ P.a = P.a := hb _ (by simp)
  have eb : σ P.b = P.b := hb _ (by simp)
  have ez : σ (zt X m) = zt X m := hb _ (by simp)
  have ec : ∀ h, InD X h → ∀ b ∈ B, σ (h b) = h b := by
    intro h hh b hbB
    refine hb _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hbB, ?_⟩))
    rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral b), ?_⟩
    rw [← semi_aeval h (RingEquiv.refl _) hh _ (fun _ _ => rfl), minpoly.aeval, map_zero]
  have l0 : ∀ b : Kb X, b ≠ 0 → lg X m b b = 0 := fun b h => l3 b b 0 h (by simp)
  have hc : cyc m s = 1 := by
    have h1 := l3 (zt X m ^ (1 : ZMod m).val) 1 1 one_ne_zero (by simp)
    have h2 := l6 σ τ s hτ hσ (zt X m ^ (1 : ZMod m).val) 1 one_ne_zero
      (by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow, one_pow])
    rw [map_pow, ez, map_one, h1, mul_one] at h2
    exact h2.symm
  have a0 : P.a ≠ 0 := fun h => hP.hu.1 ((io X).injective (by rw [← hP.ha, h, zero_pow hm.ne', map_zero]))
  have b0 : P.b ≠ 0 := fun h => hP.hv.1 ((io X).injective (by rw [← hP.hb, h, zero_pow hm.ne', map_zero]))
  refine ⟨σ, hσ, 1, by simp, fun h hh => ?_⟩
  have inv : ∀ x, σ⁻¹ (σ x) = x := fun x => σ.symm_apply_apply x
  have e : P.η (σ⁻¹ * h * σ) = P.η h := by
    refine hB _ _ (fun f => ?_) hh fun b hbB => ?_
    · show σ⁻¹ (h (σ (io X f))) = io X f
      rw [hσ, hh, ← hσ, inv]
    · show σ⁻¹ (h (σ b)) = h b
      have : σ b = b := ec 1 (fun _ => rfl) b hbB
      rw [this, ← ec h hh b hbB, inv, ec h hh b hbB]
  simp only [dif, Pt.mv, ka, hc, ea, eb, e, l0 _ a0, l0 _ b0, map_one, l0 1 one_ne_zero]
  ring
