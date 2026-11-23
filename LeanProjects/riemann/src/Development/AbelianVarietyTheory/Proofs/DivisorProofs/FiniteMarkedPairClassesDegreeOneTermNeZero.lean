import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKottwitzClassesPerMinpolyAEqOneStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.FiniteClassIntegralRoots

open Polynomial in

theorem exists_emb_isRoot' {F C E : Type} [Field F] [NumberField F] [Ring C] [Algebra F C]
    [Algebra ℚ C] [IsScalarTower ℚ F C] [FiniteDimensional F C] [Field E] [Algebra ℚ E] [IsAlgClosed E]
    (y : C) (μ : E) (h : ((minpoly ℚ y).map (algebraMap ℚ E)).IsRoot μ) :
    ∃ τ : F →+* E, ((minpoly F y).map τ).IsRoot μ := by
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hm0 : minpoly F y ≠ 0 := minpoly.ne_zero hyi

  let hq : F[X] → ℚ[X] := fun q =>
    if hirr : Irreducible q then
      haveI : Fact (Irreducible q) := ⟨hirr⟩
      minpoly ℚ (AdjoinRoot.root q)
    else 1
  have key : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors (minpoly F y),
      q ∣ (hq q).map (algebraMap ℚ F) ∧
      (((hq q).map (algebraMap ℚ E)).IsRoot μ → ∃ τ : F →+* E, (q.map τ).IsRoot μ) := by
    intro q hqm
    have hirr : Irreducible q := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqm
    haveI : Fact (Irreducible q) := ⟨hirr⟩
    have hq0 : q ≠ 0 := hirr.ne_zero
    haveI : FiniteDimensional F (AdjoinRoot q) := (AdjoinRoot.powerBasis hq0).finite
    haveI : FiniteDimensional ℚ (AdjoinRoot q) := Module.Finite.trans F _
    haveI : Algebra.IsAlgebraic ℚ (AdjoinRoot q) := Algebra.IsAlgebraic.of_finite ℚ _
    have e : hq q = minpoly ℚ (AdjoinRoot.root q) := dif_pos hirr
    rw [e]
    refine ⟨?_, fun hμ => ?_⟩
    · rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_map_algebraMap, minpoly.aeval]
    · have hne : minpoly ℚ (AdjoinRoot.root q) ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
      have hμ' : μ ∈ (minpoly ℚ (AdjoinRoot.root q)).rootSet E := by
        rw [mem_rootSet]
        refine ⟨hne, ?_⟩
        rw [aeval_def, eval₂_eq_eval_map]; exact hμ.eq_zero
      rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hμ'
      obtain ⟨ψ, hψ⟩ := hμ'
      refine ⟨(ψ : AdjoinRoot q →+* E).comp (algebraMap F _), ?_⟩
      rw [← hψ, IsRoot.def, eval_map]
      change eval₂ ((ψ : AdjoinRoot q →+* E).comp (algebraMap F _))
        ((ψ : AdjoinRoot q →+* E) (AdjoinRoot.root q)) q = 0
      rw [← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  set S := UniqueFactorizationMonoid.normalizedFactors (minpoly F y) with hS
  set H : ℚ[X] := (S.map hq).prod with hH
  have hdvd : minpoly F y ∣ H.map (algebraMap ℚ F) := by
    have h1 : minpoly F y ∣ S.prod :=
      (UniqueFactorizationMonoid.prod_normalizedFactors hm0).symm.dvd
    refine h1.trans ?_
    rw [hH, Polynomial.map_multiset_prod, Multiset.map_map]
    have := Multiset.prod_dvd_prod_of_dvd (S := S) (fun q => q) (fun q => (hq q).map (algebraMap ℚ F))
      (fun q hq' => (key q hq').1)
    simpa using this
  have hH0 : aeval y H = 0 := by
    rw [← aeval_map_algebraMap F]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, map_mul, minpoly.aeval, zero_mul]
  have hdy : minpoly ℚ y ∣ H := minpoly.dvd ℚ y hH0
  have hHμ : (H.map (algebraMap ℚ E)).IsRoot μ := by
    obtain ⟨k, hk⟩ := hdy
    rw [hk, Polynomial.map_mul, IsRoot.def, eval_mul, h.eq_zero, zero_mul]
  rw [hH, Polynomial.map_multiset_prod, IsRoot.def, Polynomial.eval_multiset_prod,
    Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.map_map] at hHμ
  obtain ⟨q, hqS, hq0⟩ := Multiset.mem_map.1 hHμ
  obtain ⟨τ, hτ⟩ := (key q hqS).2 hq0
  refine ⟨τ, ?_⟩
  have hqd : q ∣ minpoly F y := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hqS
  obtain ⟨k, hk⟩ := hqd
  rw [hk, Polynomial.map_mul, IsRoot.def, eval_mul, hτ.eq_zero, zero_mul]

theorem root_norm_le' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β y : G.Cˣ) (c : ℚˣ),
    (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β → ∀ B : ℝ, ‖((c : ℚ) : ℚ_[p])‖ ≤ B →
    ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B →
    (∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) →
    (∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) →
    ∀ μ : PadicAlgCl p, ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
      ‖μ‖ ≤ B * B := by
  intro p _ G β y c hyc B hc hc' hy hyi μ hμ
  have h0 := GlobalTheory.GlobEig.isRoot_minpoly_of_isRoot_charpoly (y : G.C) μ hμ
  obtain ⟨τ, hτ⟩ := exists_emb_isRoot' (F := G.F) (y : G.C) μ h0
  have hcpos : 0 < ‖((c : ℚ) : ℚ_[p])‖ := norm_pos_iff.2 (by simp)
  have hprod : ‖((c : ℚ) : ℚ_[p])‖ * ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, ← Rat.cast_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Rat.cast_one, norm_one]
  have hB0 : 0 ≤ B := hcpos.le.trans hc
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ B * B := by
      rw [← hprod]
      exact mul_le_mul hc hc' (norm_nonneg _) hB0
    nlinarith
  rcases GlobalTheory.GlobEig.liesOver_or_conj G τ with hu | hu
  · obtain ⟨i, ν, hνμ, hν⟩ := GlobalTheory.GlobEig.exists_root_rho G τ hu y μ hτ
    have h1 := hy i ν hν
    rw [hνμ] at h1
    nlinarith
  · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G y τ μ hτ
    obtain ⟨i, ν, hνμ, hν⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hu (sh G y) μ h2
    have h3 := GlobalTheory.GlobEig.isRoot_inv G i β y c hyc ν hν
    have h4 := hyi i _ h3
    have hs : ‖((c : ℚ) : PadicAlgCl p)‖ = ‖((c : ℚ) : ℚ_[p])‖ := by
      rw [← PadicAlgCl.norm_extends, map_ratCast]
    rw [norm_mul, norm_inv, hs, hνμ, ← div_eq_mul_inv, div_le_iff₀ hcpos] at h4
    calc ‖μ‖ ≤ B * ‖((c : ℚ) : ℚ_[p])‖ := h4
      _ ≤ B * B := mul_le_mul_of_nonneg_left hc hB0

theorem integral_of_term_ne_zero' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → ∃ N : ℕ, 0 < N ∧ ∀ P : Pair G, (∃ μ, P.Mark μ) → P.term L.K.toSubgroup f r K φ ≠ 0 → IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f r K φ hr hf hφ
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.twistedHeckeTestFunction_support_compact p G L f hf
  obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP p G (Ω ∪ Ω⁻¹) (hΩc.union hΩc.inv)
  obtain ⟨k, hk⟩ := GlobalTheory.T.twisted_orbit_norm_bounds p G r K φ hr hφ
  have hp := (Fact.out : p.Prime)
  refine ⟨D * p ^ (2 * k * Module.finrank ℚ G.C), Nat.mul_pos hD (pow_pos hp.pos _), ?_⟩
  intro P _ hP

  have fin : ∀ (y0 : G.Cˣ) (c0 : ℚˣ), (y0 : G.C) * P.β * sh G y0 = algebraMap ℚ G.C c0 * P.β →
      ‖((c0 : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k → ‖(((c0⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w (y0 : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ (w : Fin G.m) (μ : PadicAlgCl p),
        ((G.rho w ((y0⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ →
          ‖μ‖ ≤ (p : ℝ) ^ k) →
      (∀ i, ∃ kk : ℕ, ∃ a : ℤ, ((D * p ^ kk : ℕ) : ℚ) * (LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.coeff i = a) →
      IsIntegral ℤ (((D * p ^ (2 * k * Module.finrank ℚ G.C) : ℕ) : ℤ) • (y0 : G.C)) := by
    intro y0 c0 hy0 hc hc' hu hu' hAf
    have hroots := root_norm_le' p G P.β y0 c0 hy0 _ hc hc' hu hu'
    have hroots' : ∀ μ : PadicAlgCl p,
        ((LinearMap.mulLeft ℚ (y0 : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
        ‖μ‖ ≤ (p : ℝ) ^ (2 * k) := fun μ hμ => by
      rw [show 2 * k = k + k by ring, pow_add]; exact hroots μ hμ
    have h6 := GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots p _ (LinearMap.charpoly_monic _) (2 * k) hroots'
    rw [LinearMap.charpoly_natDegree] at h6
    apply GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int G.C
    intro i
    obtain ⟨kk, hkk⟩ := hAf i
    exact GlobalTheory.T.den_bound_combine_padic_primeToP p D (2 * k * Module.finrank ℚ G.C) kk hp _ (h6 i) hkk

  rw [Pair.term] at hP
  split_ifs at hP with h
  swap
  · exact absurd rfl hP
  rw [Pair.termAt, pointSum] at hP
  obtain ⟨q, hq⟩ : ∃ q, _ ≠ (0 : ℂ) := by
    by_contra hc
    push_neg at hc
    exact hP (by rw [finsum_congr hc]; exact finsum_zero)
  have hq2 := (mul_ne_zero_iff.1 hq).2
  have hfq := (mul_ne_zero_iff.1 hq2).1
  have hφq := (mul_ne_zero_iff.1 hq2).2
  set x := P.trivAf.choose with hxdef
  set o := Quotient.out q with hodef
  have hgΩ := hΩ _ hfq
  have hnrm := h.choose_spec
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk P.atP h.choose.1 h.choose.2 o.2 hnrm hφq
  set g := o.1⁻¹ * P.toAf x P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec P.self * o.1 with hg
  have hg1 : ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
      ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ *
        ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x)⁻¹ := by
    show ((o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) *
      (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 = _
    group
  set X := (o.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1⁻¹ * x
  have hA := hDp g (P.γ : G.C) X (Or.inl hgΩ) (by rw [hg1]; rfl)
  have hgi : g⁻¹ ∈ Ω ∪ Ω⁻¹ := Or.inr (by simpa using hgΩ)
  have hA' := hDp g⁻¹ ((P.γ⁻¹ : G.Cˣ) : G.C) X hgi (by
    show (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ).val = _
    rw [hg1]; simp [mul_assoc])
  have hc1 : ((P.atP.1 : ℚ_[p]ˣ) : ℚ_[p]) = ((P.c : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] (P.c : ℚ) = _
    simp
  have hc2 : ((P.atP.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) = (((P.c⁻¹ : ℚˣ) : ℚ) : ℚ_[p]) := by
    show algebraMap ℚ ℚ_[p] ((P.c⁻¹ : ℚˣ) : ℚ) = _
    simp
  have hw1 : ∀ w, (((P.atP.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w (P.γ : G.C) := fun w => rfl
  have hw2 : ∀ w, ((((P.atP.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w))) =
      G.rho w ((P.γ⁻¹ : G.Cˣ) : G.C) := fun w => rfl
  have hrel' : ((P.γ⁻¹ : G.Cˣ) : G.C) * P.β * sh G ((P.γ⁻¹ : G.Cˣ) : G.C) =
      algebraMap ℚ G.C ((P.c⁻¹ : ℚˣ) : ℚ) * P.β := (P.cent.inv_mem P.self.2).2
  refine ⟨fin P.γ P.c P.sim (hc1 ▸ hk1) (hc2 ▸ hk2) (fun w μ hμ => hk3 w μ (by rw [hw1]; exact hμ))
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ)) hA,
    fin P.γ⁻¹ P.c⁻¹ hrel' (hc2 ▸ hk2) (by rw [inv_inv]; exact hc1 ▸ hk1)
      (fun w μ hμ => hk4 w μ (by rw [hw2]; exact hμ))
      (fun w μ hμ => hk3 w μ (by rw [hw1, ← inv_inv P.γ]; exact hμ)) hA'⟩

open GlobalTheory.LKMid.Northcott in

theorem finite_pol_marked' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ N : ℕ, 0 < N →
    {P0 : Polynomial G.F | ∃ P : Pair G, (∃ μ, P.Mark μ) ∧ P.pol = P0 ∧
      IsIntegral ℤ ((N : ℤ) • (P.γ : G.C)) ∧ IsIntegral ℤ ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C))}.Finite := by
  intro p _ G hG N hN
  refine (GlobalTheory.T.finite_monic_of_roots_bdd_of_mul_isIntegral G.F G.n N N hN).subset ?_
  rintro _ ⟨P, ⟨μ, v₀, hv₀, x₀, hx₀, hpos⟩, rfl, hI1, hI2⟩
  have hc0 : ((P.c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast P.c.ne_zero
  have hnorm : ∀ (v : InfinitePlace G.F) (w : ℂ) (x : Fin G.n → ℂ), x ≠ 0 → G.psi v P.γ *ᵥ x = w • x →
      ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
    intro v w x hx hwx
    obtain ⟨-, -, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v
    obtain ⟨Z, hZ⟩ := GlobalTheory.T.similitudePair_gram_inv_congruent p G P v
    have hsig := G.sig v
    have hn := G.n_pos
    refine GlobalTheory.T.eigenvalue_normSq_of_similitude_hermitian_signature G.n (G.gram v) _ (G.psi v P.γ) (G.gram_herm v) Z ((P.c : ℚ) : ℝ) ?_ ?_ hZ hc0 ?_ ?_
      w x hx hwx
    · rcases hsig with h | h <;> omega
    · rcases hsig with h | h <;> omega
    · rw [hlaw]; congr 1
    · by_cases hv : v = v₀
      · subst hv; exact Or.inr ⟨μ, x₀, hx₀, hpos⟩
      · left
        have h1 : sigPosH (G.gram_herm v) ≠ 1 := by
          intro h1
          have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := hG.le
          have := Fintype.card_le_one_iff.1 hcard ⟨v, h1⟩ ⟨v₀, hv₀⟩
          exact hv (congrArg Subtype.val this)
        rcases hsig with h | h
        · exact absurd h.1 h1
        · exact h.1
  have hint : ∀ (v : InfinitePlace G.F) (w : ℂ) (x : Fin G.n → ℂ), x ≠ 0 → G.psi v P.γ *ᵥ x = w • x →
      IsIntegral ℤ ((N : ℂ) * w) ∧ IsIntegral ℤ ((N : ℂ) * w⁻¹) := by
    intro v w x hx hwx
    have hinv : G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) * G.psi v (P.γ : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hx' : x = w • (G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x) := by
      conv_lhs => rw [← Matrix.one_mulVec x, ← hinv, ← Matrix.mulVec_mulVec, hwx, Matrix.mulVec_smul]
    have hw0 : w ≠ 0 := by
      rintro rfl; apply hx; rw [hx', zero_smul]
    have hinvx : G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x = w⁻¹ • x := by
      calc _ = w⁻¹ • (w • (G.psi v ((P.γ⁻¹ : G.Cˣ) : G.C) *ᵥ x)) := by
            rw [smul_smul, inv_mul_cancel₀ hw0, one_smul]
        _ = w⁻¹ • x := by rw [← hx']
    constructor
    · refine isIntegral_eig (hI1.map (G.psi v).toIntAlgHom) hx ?_
      change G.psi v ((N : ℤ) • (P.γ : G.C)) *ᵥ x = _
      rw [map_zsmul, Matrix.smul_mulVec, hwx, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      push_cast; rfl
    · refine isIntegral_eig (hI2.map (G.psi v).toIntAlgHom) hx ?_
      change G.psi v ((N : ℤ) • ((P.γ⁻¹ : G.Cˣ) : G.C)) *ᵥ x = _
      rw [map_zsmul, Matrix.smul_mulVec, hinvx, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      push_cast; rfl
  have hkey : ∀ (v : InfinitePlace G.F) (w : ℂ), P.pol.eval₂ v.embedding w = 0 →
      ‖w‖ ≤ N ∧ IsIntegral ℤ ((N : ℂ) * w) := by
    intro v w hw
    obtain ⟨x, hx, hwx⟩ := GlobalTheory.T.exists_eigenvector_of_minpoly_root_hermitianPsi p G P v w hw
    obtain ⟨h2, h3⟩ := hint v w x hx hwx
    exact ⟨norm_le_of_isIntegral_inv w P.c N hN (hnorm v w x hx hwx) hc0 h3, h2⟩
  refine ⟨minpoly.monic (Algebra.IsIntegral.isIntegral _), P.reg.1, ?_⟩
  intro φ w hw
  have hr : P.pol.eval₂ φ w = 0 := by
    have := (Polynomial.mem_roots'.1 hw).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [← h] at hr; exact hkey _ w hr
  · have hr' : P.pol.eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ w) = 0 := by
      rw [h]
      have := congrArg (starRingEnd ℂ) hr
      rw [map_zero, Polynomial.hom_eval₂] at this
      convert this using 2
      exact RingHom.ext fun x => rfl
    obtain ⟨h1, h2⟩ := hkey _ _ hr'
    refine ⟨by simpa using h1, ?_⟩
    have := h2.map (starRingEnd ℂ).toIntAlgHom
    simpa using this

theorem finite_cls_term_one_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → Set.Finite {Q : Cls G | (∃ μ, (Quot.out Q).Mark μ) ∧ (Quot.out Q).term L.K.toSubgroup f 1 K' f' ≠ 0} := by
  intro p _ G ha L f hf hreg K' f' hf'
  obtain ⟨N, hN, hb⟩ := integral_of_term_ne_zero' p G L f 1 K' f' one_pos hf hf'
  have hS := finite_pol_marked' p G ha N hN
  refine (hS.biUnion (fun P0 _ => GlobalTheory.T.finite_kottwitz_classes_per_minpoly_a_eq_one p G ha L f hf hreg K' f' hf' P0)).subset ?_
  rintro q ⟨hm, ht⟩
  obtain ⟨h1, h2⟩ := hb (Quot.out q) hm ht
  exact Set.mem_biUnion (x := (Quot.out q).pol) ⟨Quot.out q, hm, rfl, h1, h2⟩ ⟨rfl, hm, ht⟩

end GlobalTheory.LKCx.FiniteClassIntegralRoots
