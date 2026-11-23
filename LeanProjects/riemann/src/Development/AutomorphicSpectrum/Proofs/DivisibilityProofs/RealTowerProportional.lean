import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLinearFunctionalsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreementStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace RealProp

theorem map_monomial_eq_zero {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (h : ∀ c : J → ℝ, Φ ((-∑ x, C (c x) * X x) ^ d) = 0) (m : J →₀ ℕ) (hm : m.degree = d) :
    Φ (monomial m 1) = 0 := by
  obtain ⟨Pl, -, hev, hco, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound J d Φ
  have hP : Pl = 0 := MvPolynomial.funext fun c => by rw [hev c, h c, map_zero]
  have h0 := hco m hm
  rw [hP, coeff_zero] at h0
  have hmul : ((m.multinomial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have hpow : ((-1 : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp h0.symm).resolve_left (mul_ne_zero hpow hmul)

theorem eval_toWt {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (P : MvPolynomial (Ψ × Fin N) ℝ) :
    eval lam (PB.toWt P) = eval (PB.gap lam) P := by
  unfold PB.toWt
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, eval_X, PB.gap]

theorem eval_degPoly_comap_some {e : ℕ} {σ : Type} [Fintype σ] (S : PB.AnSys e (Option σ)) (c : σ → ℝ) :
    eval c (S.comap some).degPoly = eval (fun o : Option σ => o.elim 0 c) S.degPoly := by
  simp only [PB.AnSys.degPoly, PB.formPoly, map_sum, map_mul, map_prod, eval_C, eval_X]
  refine Fintype.sum_of_injective (fun w j => some (w j)) ?_ _ _ ?_ ?_
  · intro w w' hw
    funext j
    exact Option.some_injective _ (congrFun hw j)
  · intro b hb
    have : ∃ j, b j = none := by
      by_contra hne
      exact hb ⟨fun j => (b j).get (Option.ne_none_iff_isSome.mp fun h => hne ⟨j, h⟩), funext fun j => by simp⟩
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), mul_zero]
  · intro w
    rfl

theorem exists_flagDeg_eq (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : Wt Ψ N, flagDeg lam = c * eval (fun x : Ψ × Fin N => lam x.1 x.2) (antisymDelta Ψ N) := by
  refine ⟨((dimFl Ψ N).factorial : ℝ) * ∏ τ : Ψ, ∏ i : Fin N, ∏ k : Fin N,
      (if i < k then (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ))⁻¹ else 1), ?_, ?_⟩
  · refine mul_pos (by exact_mod_cast Nat.factorial_pos _)
      (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_)
    split_ifs with h
    · have : ((i : ℕ) : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast h
      exact inv_pos.2 (by linarith)
    · exact one_pos
  · intro lam
    rw [(flagDeg_eq_weyl Ψ N lam).1, mul_assoc]
    congr 1
    simp only [antisymDelta, map_prod, map_sub, eval_X]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hsplit : ∀ k : Fin N, (if i < k then (lam τ i - lam τ k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1)
        = (if i < k then (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ))⁻¹ else 1) * (if i < k then lam τ i - lam τ k else 1) := by
      intro k
      split_ifs <;> ring
    rw [Finset.prod_congr rfl fun k _ => hsplit k, Finset.prod_mul_distrib]
    congr 1
    simp [Finset.prod_ite, Finset.filter_lt_eq_Ioi]

theorem rhoWt_regDominant (Ψ : Type) [Fintype Ψ] (N : ℕ) : RegDominant (rhoWt : Wt Ψ N) := by
  intro τ a b hab
  have h : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [rhoWt]
  linarith

theorem RealTie_n_pos {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {M : RootModel Ψ N}
    {S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))} {n : ℕ} (R : RealTie M S n) : 0 < n := by
  exact Nat.pos_of_ne_zero fun hn => M.δ_pos.ne' (R.δ_eq.trans (mul_eq_zero.2 (Or.inl hn)))

theorem lin_eq_zero {J : Type} (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (h : ∀ m, Φ (monomial m 1) = 0) : Φ = 0 := by
  refine (MvPolynomial.basisMonomials J ℝ).ext fun m => ?_
  rw [MvPolynomial.coe_basisMonomials, LinearMap.zero_apply]
  exact h m

theorem degree_mapDomain_some {J : Type} (m : J →₀ ℕ) : (m.mapDomain some).degree = m.degree := by
  classical
  show ∑ i ∈ (m.mapDomain some).support, (m.mapDomain some) i = ∑ i ∈ m.support, m i
  rw [Finsupp.mapDomain_support_of_injective (Option.some_injective _), Finset.sum_image
    (fun x _ y _ hxy => Option.some_injective _ hxy)]
  exact Finset.sum_congr rfl fun x _ => Finsupp.mapDomain_apply (Option.some_injective _) m x

theorem geoFun_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.geoFun (monomial m 1) = M.geoMono m := by
  have := (MvPolynomial.basisMonomials (Option (Ψ × Fin N)) ℝ).constr_basis ℝ M.geoMono m
  rw [MvPolynomial.coe_basisMonomials] at this
  exact this

theorem geoFun_monomial_of_ne {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (m : Option (Ψ × Fin N) →₀ ℕ)
    (h : m.degree ≠ dimFl Ψ N) : M.geoFun (monomial m 1) = 0 := by
  rw [geoFun_monomial, RootModel.geoMono, if_neg h]

theorem neg_sum_eq_linA {Ψ : Type} [Fintype Ψ] {N : ℕ} (a : Option (Ψ × Fin N) → ℝ) :
    (-∑ x, C (a x) * X x : RPA Ψ N) = linA (fun τ i => a (some (τ, i))) (-a none) := by
  simp only [linA, toA, linRoot, Fintype.sum_option, map_neg, map_sum, map_mul, rename_C, rename_X]
  ring

theorem dimFl_eq_antisymDegree (Ψ : Type) [Fintype Ψ] (N : ℕ) : dimFl Ψ N = antisymDegree Ψ N := by
  rw [dimFl, antisymDegree, Nat.choose_two_right]

theorem toA_linRoot_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (d : ℕ) :
    toA (linRoot lam ^ d) = linA lam 0 ^ d := by
  simp only [linA, map_zero, zero_mul, add_zero, toA, map_pow]

theorem exists_geoFun_eq (hProp : PB.Proportional) (hI : PB.Inputs) (II : IntersectionSystem)
    (hII : IsFullIntersectionSystem II) {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} [Nonempty Ψ]
    {T : RootTower Ψ N} (R : RealTower T) (hU : R.Unif) (c : T.Comp) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (B : ℕ) (lam : Wt Ψ N),
      (T.M B c).geoFun (toA (linRoot lam ^ dimFl Ψ N)) = κ * flagDeg lam := by
  have hN2 : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  obtain ⟨⟨c0, hc0, hdeg⟩, hall⟩ := hProp hI Ψ N T.j hN2 T.j_lt.le
  obtain ⟨hvol, htoWt⟩ := hall (dimFl Ψ N) ((R.Sys c).comap some) (dimFl_eq_antisymDegree Ψ N) (hU c)
  obtain ⟨cf, hcf, hflag⟩ := exists_flagDeg_eq Ψ N
  have hnR : (0 : ℝ) < (R.n c : ℝ) := by exact_mod_cast RealTie_n_pos (R.tie 0 c)
  refine ⟨PB.volOf ((R.Sys c).comap some) * c0 / ((R.n c : ℝ) * cf),
    div_pos (mul_pos hvol hc0) (mul_pos hnR hcf), fun B lam => ?_⟩
  have key := GlobalTheory.T.real_tower_geometric_agreement hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) lam 0
  rw [zero_div, ← toA_linRoot_pow] at key
  have e1 : eval (PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) 0) (R.Sys c).degPoly
      = PB.volOf ((R.Sys c).comap some) * c0 * eval (fun x : Ψ × Fin N => lam x.1 x.2) (antisymDelta Ψ N) := by
    show eval (fun o : Option (Ψ × Fin N) => o.elim 0 (PB.gap fun x : Ψ × Fin N => lam x.1 x.2)) (R.Sys c).degPoly = _
    rw [← eval_degPoly_comap_some (R.Sys c) (PB.gap fun x : Ψ × Fin N => lam x.1 x.2),
      ← eval_toWt (fun x : Ψ × Fin N => lam x.1 x.2), htoWt, hdeg]
    simp only [map_mul, eval_C]
    ring
  have key2 := key.trans e1
  rw [hflag lam, div_mul_eq_mul_div, eq_div_iff (mul_pos hnR hcf).ne']
  linear_combination cf * key2

end RealProp

open RealProp in

theorem rootTower_proportional_of_unif : PB.Proportional → PB.Inputs → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N)
    (R : RealTower T), R.Unif → T.Proportional := by
  intro hProp hI II hII Ψ _ _ N _ T R hU
  have hrho : 0 < flagDeg (rhoWt : Wt Ψ N) := (flagDeg_eq_weyl Ψ N rhoWt).2.1 (rhoWt_regDominant Ψ N)
  have hvol : ∀ c : T.Comp, ∃ κ : ℝ, 0 < κ ∧ T.vol c = κ ∧ ∀ (B : ℕ) (lam : Wt Ψ N),
      (T.M B c).geoFun (toA (linRoot lam ^ dimFl Ψ N)) = κ * flagDeg lam := by
    intro c
    obtain ⟨κ, hκ, h⟩ := exists_geoFun_eq hProp hI II hII R hU c
    refine ⟨κ, hκ, ?_, h⟩
    rw [RootTower.vol, h, mul_div_assoc, div_self hrho.ne', mul_one]
  obtain ⟨Φd, hΦd⟩ := (GlobalTheory.T.flag_degree_linear_functionals Ψ N).1
  refine ⟨fun c => ?_, fun B c F => ?_, fun B B' c => ?_⟩
  · obtain ⟨κ, hκ, hv, -⟩ := hvol c
    rw [hv]
    exact hκ
  · obtain ⟨κ, -, hv, h⟩ := hvol c
    rw [hv]
    have hL : (T.M B c).geoFun ∘ₗ (rename (R := ℝ) (Option.some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap
        - κ • Φd = 0 := by
      apply lin_eq_zero
      intro m
      by_cases hm : m.degree = dimFl Ψ N
      · refine map_monomial_eq_zero (dimFl Ψ N) _ (fun a => ?_) m hm
        have hlin : (-∑ x, C (a x) * X x : MvPolynomial (Ψ × Fin N) ℝ) = linRoot (fun τ i => a (τ, i)) := rfl
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
          hΦd, smul_eq_mul]
        rw [hlin]
        have h1 := h B (fun τ i => a (τ, i))
        simp only [toA] at h1
        rw [h1, flagDeg, sub_self]
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
          hΦd, smul_eq_mul, rename_monomial]
        rw [geoFun_monomial_of_ne _ _ (by rwa [degree_mapDomain_some]),
          (GlobalTheory.T.flag_degree_linear_functionals Ψ N).2.2.2 _ _ (isHomogeneous_monomial _ rfl) hm, mul_zero, sub_zero]
    have h2 := LinearMap.congr_fun hL F
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      hΦd, smul_eq_mul, LinearMap.zero_apply] at h2
    simp only [toA]
    exact sub_eq_zero.mp h2
  · have hnR : (0 : ℝ) < (R.n c : ℝ) := by exact_mod_cast RealTie_n_pos (R.tie 0 c)
    have hL : (T.M B c).geoFun - (T.M B' c).geoFun = 0 := by
      apply lin_eq_zero
      intro m
      by_cases hm : m.degree = dimFl Ψ N
      · refine map_monomial_eq_zero (dimFl Ψ N) _ (fun a => ?_) m hm
        rw [LinearMap.sub_apply, sub_eq_zero, neg_sum_eq_linA]
        have k1 := GlobalTheory.T.real_tower_geometric_agreement hI II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c)
          (fun τ i => a (some (τ, i))) (-a none)
        have k2 := GlobalTheory.T.real_tower_geometric_agreement hI II hII Ψ N (T.M B' c) (R.Sys c) (R.n c) (R.tie B' c)
          (fun τ i => a (some (τ, i))) (-a none)
        rw [R.kA_eq B B' c, ← k2] at k1
        exact mul_left_cancel₀ hnR.ne' k1
      · rw [LinearMap.sub_apply, geoFun_monomial_of_ne _ _ hm, geoFun_monomial_of_ne _ _ hm, sub_zero]
    exact sub_eq_zero.mp hL

end GlobalTheory.CompanionTheory.Ar.Top
