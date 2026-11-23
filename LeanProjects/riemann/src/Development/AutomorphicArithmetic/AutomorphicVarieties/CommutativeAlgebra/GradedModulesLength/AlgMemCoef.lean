import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.AdmissibleMonoIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TwoSigned
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.AdmissibilityHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GradedQuotientIsomorphism
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleUB
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerIndependenceOfOrder
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleNzd
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem self_isGr {k : ℕ} (X : HidaSetting k) : (GMod.self X.𝒜).IsGr X.𝒜 where
  smul_mem ha hx := X.gra.toGradedMonoid.toGradedMul.mul_mem ha hx
  internal := DirectSum.Decomposition.isInternal X.𝒜
  fin := Module.Finite.self X.R

private theorem chain {k : ℕ} (X : HidaSetting k) (ts : List (Deg k × X.R)) (J : Ideal X.R) (a : X.R)
    (hJ : (GMod.self X.𝒜).IsHomSub J) (hv : Valid X.𝒜 (ts ++ [(0, a)]))
    (hn : ∀ p : X.R, a * p ∈ J → p ∈ J) (hadm : admitted X.𝒜 (ts ++ [(0, a)]) J) :
    ∀ᶠ d in atTop, chi ts (((GMod.self X.𝒜).quo J).quot a) d ≤
      chi [(0, a)] ((GMod.self X.𝒜).quo (J ⊔ secs ts)) d := by
  have hF : ((GMod.self X.𝒜).quo J).IsGr X.𝒜 := ((ruleGr k X _ (self_isGr X)).1 J hJ).2
  have hA : admitted X.𝒜 (ts ++ [(0, a)]) ((GMod.self X.𝒜).quo J).Ann := by
    obtain ⟨N, hN⟩ := hadm
    refine ⟨N, hN.trans (sup_le_sup_right ?_ _)⟩
    exact (Ideal.annihilator_quotient (I := J)).ge
  have h1 := ruleNzd k X ts ((GMod.self X.𝒜).quo J) 0 a (by
    intro x hx
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective J x
    have h : Submodule.Quotient.mk (p := J) (a * p) = 0 := hx
    exact (Submodule.Quotient.mk_eq_zero J).2 (hn p ((Submodule.Quotient.mk_eq_zero J).1 h)))
  have h2 := euler_rule_two_of_graded_finite_iso ruleGr ruleFin ruleIso (euler_additivity_of_rules ruleGr ruleFin ruleIso) k X (ts ++ [(0, a)]) ((0, a) :: ts) _ hv
    (List.perm_append_singleton _ _) hF hA
  have h3 := ruleUB k X ts [(0, a)] _ hv hF hA
  obtain ⟨iso⟩ := qi_holds k X.B X.R X.𝒜 J ts
  filter_upwards [h2, h3] with d h2 h3
  rw [← h1, ← h2, ← ruleIso k X _ _ _ iso]
  exact h3

private theorem hom_sup {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] (𝒜 : Deg k → Submodule B R)
    (ts : List (Deg k × R)) (J : Ideal R) (hJ : (GMod.self 𝒜).IsHomSub J) (hv : Valid 𝒜 ts) :
    (GMod.self 𝒜).IsHomSub (J ⊔ secs ts : Ideal R) := by
  have hJ' : J = Submodule.span R {x : R | x ∈ J ∧ ∃ m, x ∈ 𝒜 m} := hJ
  show J ⊔ secs ts = Submodule.span R {x : R | x ∈ J ⊔ secs ts ∧ ∃ m, x ∈ 𝒜 m}
  refine le_antisymm (sup_le ?_ ?_) (Submodule.span_le.2 fun x hx => hx.1)
  · exact hJ'.le.trans (Submodule.span_mono fun x hx => ⟨Submodule.mem_sup_left hx.1, hx.2⟩)
  · refine Submodule.span_mono ?_
    rintro x ⟨d, hd⟩
    exact ⟨Submodule.mem_sup_right (Ideal.subset_span ⟨d, hd⟩), d, (hv _ hd).2⟩

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private theorem coef_hom (J : Ideal A) : (GMod.self (reesGr N)).IsHomSub (coefIdeal N J) := by
  classical
  refine le_antisymm (fun p hp => ?_) (Submodule.span_le.2 fun x hx => hx.1)
  rw [eq_sum_mono N p]
  refine Submodule.sum_mem _ fun μ _ => Submodule.subset_span ⟨fun n => ?_, _, mono_mem N μ _ _⟩
  show MvPolynomial.coeff n (MvPolynomial.monomial μ _) ∈ J
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hp μ
  · exact J.zero_mem

private theorem coeff_alg (b : B) (p : rees N) (n : Fin k →₀ ℕ) :
    MvPolynomial.coeff n (algebraMap B (rees N) b * p).1 = algebraMap B A b * MvPolynomial.coeff n p.1 := by
  show MvPolynomial.coeff n (algebraMap B (MvPolynomial (Fin k) A) b * p.1) = _
  rw [MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul]

private theorem alg_mem_coef (J : Ideal A) (b : B) (hb : algebraMap B A b ∈ J) :
    algebraMap B (rees N) b ∈ coefIdeal N J := fun n => by
  rw [← mul_one (algebraMap B (rees N) b), coeff_alg]
  exact J.mul_mem_right _ hb

end

private theorem ts_valid {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} [GradedAlgebra 𝒜]
    {x : A →ₐ[O] O} {r s r' s' m : ℕ} (Q : Eqns 𝒜 x r s r' s' m) : Valid (mGr Q) (ts Q) := by
  intro p hp
  simp only [ts, tsF, tsR, List.mem_append, List.mem_ofFn, List.mem_singleton] at hp
  rcases hp with ⟨i, rfl⟩ | ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl
  exacts [⟨e_nonneg _, sec_mem _ _ _ (sq_mem_neg 𝒜 (Q.hF _))⟩, ⟨e_nonneg _, sec_mem _ _ _ (Q.hG i)⟩,
    ⟨e_nonneg _, sec_mem _ _ _ (sq_mem_pos 𝒜 (Q.hE i))⟩, ⟨e_nonneg _, sec_mem _ _ _ (Q.hE' i)⟩,
    ⟨e_nonneg _, sec_mem _ _ _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))⟩]

theorem UpperTheory.V.Alg.M.core_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    (∀ i, φ (Q.Z i) = 0) → 1 ≤ r → (∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j) → ∀ ϖ : O, Irreducible ϖ →
    ∀ (y : Fin r → A) (c : Fin r → ℕ), (∀ i, y i ∈ 𝒜 (-1) ∧ Q.F i.castSucc - ϖ ^ c i • y i ∈ satSq x) → Q.F (Fin.last r) ∈ satSq x →
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal →
    ∀ a : A, M5 𝒜 K x Q.ideal a → φ a ≠ 0 → ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T →
      ((∑ i, c i : ℕ) : ℝ) ≤ 2 * ∑ ξ ∈ T, v (ξ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hZ hr hd ϖ hϖ y c hy hF s1 s2 m2 m3 m4
    a m5 ha T hT
  lift a to 𝒜 0 using m5.1
  have hfg : ∀ i, (mN 𝒜 (Q.F (Fin.last r)) i).FG := by
    have h := fg_holds O A 𝒜 x hW
    intro i
    fin_cases i
    · exact h _
    · exact h _
    · exact (Submodule.fg_span_singleton _).sup (((h _).mul (h _)).mul (h _))
  let X : HidaSetting 3 := { B := 𝒜 0, R := mR Q, 𝒜 := mGr Q, std := std_holds _ _ _ _ hfg }
  set J : Ideal (mR Q) := coefIdeal _ (RingHom.ker φ) with hJ
  have hZJ : ∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J := fun i => alg_mem_coef _ _ _ (hZ i)
  have hadm := admissibility_holds O K A 𝒜 x hW r s r' s' m Q s1 s2 m2 m3 a m5 J hZJ
  have hval : Valid (mGr Q) (ts Q ++ [(0, algebraMap (𝒜 0) (mR Q) a)]) := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact ts_valid Q p hp
    · rw [List.mem_singleton.1 hp]
      exact ⟨le_rfl, SetLike.algebraMap_mem_graded _ a⟩
  have hn : ∀ p : mR Q, algebraMap (𝒜 0) (mR Q) a * p ∈ J → p ∈ J := fun p hp n => by
    have h := hp n
    rw [coeff_alg, RingHom.mem_ker, map_mul] at h
    exact (mul_eq_zero.1 h).resolve_left ha
  have hadm' : admitted (mGr Q) (ts Q) (J ⊔ Ideal.span {algebraMap (𝒜 0) (mR Q) a}) := by
    refine E2.admissible_tail_of_cons_mem (mGr Q) (d := 0) (s := algebraMap (𝒜 0) (mR Q) a) (J := J) ?_ le_sup_left
      (Submodule.mem_sup_right (Ideal.subset_span rfl))
    obtain ⟨N, hN⟩ := hadm
    exact ⟨N, by rwa [E2.secs_perm (List.perm_append_singleton _ _)] at hN⟩
  have h1 := low_holds O A 𝒜 x hW r s r' s' m Q τ wt φ hφ hr hd ϖ hϖ y c hy hF a m5.2.1 hadm'
  have h2 := chain X (ts Q) J _ (coef_hom _ _) hval hn hadm
  have h3 := up_holds O K v hv A 𝒜 x hW r s r' s' m Q s1 s2 m2 m3 m4 a m5 T hT (J ⊔ secs (ts Q))
    (hom_sup _ _ _ (coef_hom _ _) (ts_valid Q)) le_sup_right fun i => Submodule.mem_sup_left (hZJ i)
  obtain ⟨d, h1, h2, h3⟩ := (h1.and (h2.and h3)).exists
  have h4 : ((((∑ i, c i : ℕ) : ℤ) * 2 ^ (r + r') : ℤ) : ℝ) ≤ 2 ^ (r + 1 + r') * ∑ ξ ∈ T, v (ξ a) :=
    (Int.cast_le.2 (h1.trans h2)).trans h3
  have h5 : (0 : ℝ) < 2 ^ (r + r') := by positivity
  refine le_of_mul_le_mul_right ?_ h5
  rw [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat] at h4
  refine h4.trans (le_of_eq ?_)
  ring
