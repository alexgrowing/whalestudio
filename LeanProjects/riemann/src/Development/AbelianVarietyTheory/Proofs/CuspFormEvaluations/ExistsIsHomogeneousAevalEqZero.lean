import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FnFGFnTrdeg

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.SecRelation

theorem coeff_aeval_C_mul_X {K Ω σ : Type} [Field K] [Field Ω] [Algebra K Ω] [Fintype σ] (v : σ → Ω)
    (P : MvPolynomial σ K) (d : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff d =
      MvPolynomial.aeval v (MvPolynomial.homogeneousComponent d P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    have h : MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) (MvPolynomial.monomial s a) =
        Polynomial.C (MvPolynomial.aeval v (MvPolynomial.monomial s a)) * Polynomial.X ^ s.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow,
        Polynomial.algebraMap_apply, Finsupp.degree_apply, mul_assoc]
    rw [h, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

theorem exists_isHomogeneous_aeval_eq_zero {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (hD : Algebra.trdeg K Ω = D) (hm : D + 2 ≤ m) (v : Fin m → Ω) :
    ∃ (Q : MvPolynomial (Fin m) K) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval v Q = 0 := by
  have htr : Algebra.trdeg K (Polynomial Ω) = ((D + 1 : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq K Ω (A := Polynomial Ω), Polynomial.trdeg_of_isDomain, hD]
    push_cast
    rfl
  have hdep : ¬ AlgebraicIndependent K (fun i => Polynomial.C (v i) * Polynomial.X) := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin, Nat.cast_le] at h1
    omega
  rw [algebraicIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨P, hP, hP0⟩ := hdep
  have hex : ∃ d, MvPolynomial.homogeneousComponent d P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hP0
    rw [← MvPolynomial.sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun d _ => hall d
  obtain ⟨d, hd⟩ := hex
  refine ⟨_, d, hd, MvPolynomial.homogeneousComponent_isHomogeneous d P, ?_⟩
  rw [← coeff_aeval_C_mul_X, hP, Polynomial.coeff_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    rw [map_one]
  · show (1 : p.R) = wchar (ex Dw 0 0) t * 1
    have : ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 = fun _ => 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem multiset_prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) (s : Multiset σ) :
    (s.map u).prod ∈ sec Xo c (s.card • a) (s.card • n) := by
  induction s using Multiset.induction_on with
  | empty => simpa using one_mem_sec
  | cons i s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul', succ_nsmul']
    exact sec_mul Xo c _ _ _ _ (hu i) ih

theorem aeval_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) {Q : MvPolynomial σ c.F} {d : ℕ} (hQ : Q.IsHomogeneous d) :
    MvPolynomial.aeval u Q ∈ sec Xo c (d • a) (d • n) := by
  classical
  rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hc : s.toMultiset.card = d := by
    rw [Finsupp.card_toMultiset]
    have := hQ (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h1 := multiset_prod_mem_sec u hu s.toMultiset
  rw [hc, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])] at h1
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h1

theorem exists_algHom_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    ∃ ψ : Rul Xo c →ₐ[c.F] S, ∀ f, evR Xo c f y = ψ f :=
  ⟨AlgHom.ofLinearMap (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
    (evalAt_one _ _ y h) (fun f g => evalAt_mul _ _ f g y), fun _ => rfl⟩

theorem exists_homogeneous_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ), Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) + 2 ≤ m → ∀ u : Fin m → Rul Xo c, (∀ i, u i ∈ sec Xo c a n) → ∃ (Q : MvPolynomial (Fin m) c.F) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval u Q = 0 := by
  intro E _ _ _ H Dw l Xo c a n m hm u hu
  classical
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).2
  haveI := CompFin.finite_comp Xo c
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  choose Q d hQ0 hQd hQv using fun Z : Comp Xo c =>
    exists_isHomogeneous_aeval_eq_zero (htr Z) hm (fun i => evC h Z (u i))
  have hhom : (∏ Z, Q Z).IsHomogeneous (∑ Z, d Z) := MvPolynomial.IsHomogeneous.prod _ _ _ fun Z _ => hQd Z
  refine ⟨∏ Z, Q Z, ∑ Z, d Z, Finset.prod_ne_zero_iff.2 fun Z _ => hQ0 Z, hhom, ?_⟩
  refine GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) _ _ _ (aeval_mem_sec u hu hhom) fun Z => ?_
  obtain ⟨ψ, hψ⟩ := exists_algHom_evR (genFr h Z) (hL.test _ _)
  have h1 : ψ (MvPolynomial.aeval u (Q Z)) = 0 := by
    rw [← hQv Z, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun v => MvPolynomial.aeval v (Q Z)) (funext fun i => (hψ (u i)).symm)
  show evR Xo c _ (genFr h Z) = 0
  rw [hψ, map_prod, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ Z) h1

end GlobalTheory.SecRelation
