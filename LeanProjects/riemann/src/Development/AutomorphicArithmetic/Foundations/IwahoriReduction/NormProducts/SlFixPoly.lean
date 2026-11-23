import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTraceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.BddOrder

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.EisensteinBasis
open Filter Topology

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

end UpperTheory.Kd.K4.EisensteinBasis

namespace UpperTheory.Kd.K4.EisensteinBasis

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem sl_fix (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) (a : RatFunc Ω) :
    X.sl (ofSL γ) ((jRat X Γ' a : lev X Γ') : X.K) = (jRat X Γ' a : lev X Γ') := by
  have hj : X.sl (ofSL γ) X.jK = X.jK := by
    have h1 := (jPoly X ⊤ Polynomial.X).2
    simp [jPoly, lev, Subfield.mem_iInf, RingHom.mem_eqLocusField] at h1
    have h3 := h1 γ
    erw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h3
    exact h3
  have hc : ∀ c : Ω, X.sl (ofSL γ) ((levConst X Γ' c : lev X Γ') : X.K) = (levConst X Γ' c : lev X Γ') := by
    intro c
    have h2 : ((levConst X Γ' c : lev X Γ') : X.K) = algebraMap Ω X.K c := rfl
    rw [h2, AlgEquiv.commutes]
  have hp : ∀ p : Polynomial Ω, X.sl (ofSL γ) ((jPoly X Γ' p : lev X Γ') : X.K) = (jPoly X Γ' p : lev X Γ') := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, Subfield.coe_add, hp, hq]
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [jPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      push_cast
      rw [map_mul, map_pow, hc]
      erw [hj]
  induction a using RatFunc.induction_on with
  | f p q hq =>
    simp only [jRat, RatFunc.liftRingHom_apply_div]
    push_cast
    rw [map_div₀]
    erw [hp p, hp q]

private theorem sl_stable (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) {f : X.K} (hf : f ∈ lev X (CongruenceSubgroup.Gamma M)) :
    X.sl (ofSL γ) f ∈ lev X (CongruenceSubgroup.Gamma M) := by
  have hmem : ∀ (Γ : Subgroup SL(2, ℤ)) (g : X.K), g ∈ lev X Γ ↔ ∀ δ ∈ Γ, X.sl (ofSL δ) g = g := by
    intro Γ g
    simp [lev, Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rw [hmem] at hf ⊢
  intro δ hδ
  have hconj : γ * δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ
  have heq : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← X.sl_mul, ← map_mul, heq, map_mul, X.sl_mul, hf _ hconj]

private theorem sl_inv (X : Tower Ω ε) (γ : SL(2, ℤ)) (f : X.K) : X.sl (ofSL γ⁻¹) (X.sl (ofSL γ) f) = f := by
  rw [← X.sl_mul, ← map_mul, mul_inv_cancel, map_one, X.sl_one]

private noncomputable def resE (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) :
    lev X (CongruenceSubgroup.Gamma M) ≃+* lev X (CongruenceSubgroup.Gamma M) where
  toFun f := ⟨X.sl (ofSL γ) f, sl_stable X M γ f.2⟩
  invFun f := ⟨X.sl (ofSL γ⁻¹) f, sl_stable X M γ⁻¹ f.2⟩
  left_inv f := Subtype.ext (sl_inv X γ f)
  right_inv f := Subtype.ext (by simpa using sl_inv X γ⁻¹ f)
  map_mul' f g := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

attribute [local instance] algRat

private noncomputable def resA (X : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) :
    lev X (CongruenceSubgroup.Gamma M) ≃ₐ[RatFunc Ω] lev X (CongruenceSubgroup.Gamma M) :=
  AlgEquiv.ofRingEquiv (f := resE X M γ) fun a => Subtype.ext (sl_fix X _ γ a)

end UpperTheory.Kd.K4.EisensteinBasis

private theorem jPoly_coe_eq_aeval_jK {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (Γ' : Subgroup SL(2, ℤ)) (p : Polynomial Ω) :
    ((jPoly X Γ' p : lev X Γ') : X.K) = Polynomial.aeval X.jK p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Subfield.coe_add, hp, hq]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [jPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    push_cast
    rfl

private theorem jRat_coe_div_eq_aeval_div_aeval {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (Γ' : Subgroup SL(2, ℤ)) (p q : Polynomial Ω) :
    ((jRat X Γ' (algebraMap (Polynomial Ω) (RatFunc Ω) p / algebraMap (Polynomial Ω) (RatFunc Ω) q) :
      lev X Γ') : X.K) = Polynomial.aeval X.jK p / Polynomial.aeval X.jK q := by
  simp only [jRat, RatFunc.liftRingHom_apply_div]
  rw [Subfield.coe_div, jPoly_coe_eq_aeval_jK, jPoly_coe_eq_aeval_jK]

private theorem eventually_eq_of_mero_coe_eq {τ : ℂ} (hτ : τ ∈ Hs) {f g : ℂ → ℂ} (h : (f : Mero) = g) :
    ∀ᶠ y in nhdsWithin τ {τ}ᶜ, f y = g y := by
  rw [Filter.Germ.coe_eq] at h
  have h1 := (mem_codiscreteWithin.1 h) τ hτ
  have h2 : Hs ∈ nhdsWithin τ {τ}ᶜ := mem_nhdsWithin_of_mem_nhds (H3.isOpen_Hs_place.mem_nhds hτ)
  filter_upwards [h2, Filter.disjoint_principal_right.1 h1] with y hy1 hy2
  by_contra hne
  exact hy2 ⟨hy1, hne⟩

private theorem analyticOrderAt_finite_of_mero_ne_zero {τ : ℂ} (hτ : τ ∈ Hs) {b : ℂ → ℂ} (hd : DifferentiableOn ℂ b Hs)
    (hb : (b : Mero) ≠ 0) : analyticOrderAt b τ ≠ ⊤ := by
  intro htop
  apply hb
  have hE := (hd.analyticOnNhd H3.isOpen_Hs_place).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    H3.isConnected_Hs_place.isPreconnected hτ (analyticOrderAt_eq_top.1 htop)
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  have hmem : Hs ∈ Filter.codiscreteWithin Hs := by
    rw [mem_codiscreteWithin]
    intro x _
    simp
  filter_upwards [hmem] with y hy
  exact hE hy

private theorem mero_coe_ne_zero_of_analyticOrderAt_finite {τ : ℂ} (hτ : τ ∈ Hs) {b : ℂ → ℂ} (hd : DifferentiableOn ℂ b Hs)
    (hb : analyticOrderAt b τ ≠ ⊤) : (b : Mero) ≠ 0 := by
  intro h
  rw [← Filter.Germ.coe_zero] at h
  have h1 := eventually_eq_of_mero_coe_eq hτ h
  have ha : AnalyticAt ℂ b τ := (hd.analyticOnNhd H3.isOpen_Hs_place) τ hτ
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h2 | h2
  · exact hb (analyticOrderAt_eq_top.2 h2)
  · obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
    exact hy2 hy1

private theorem valuation_eq_one_of_mem_of_inv_mem {K : Type} [Field K] (W : ValuationSubring K) {z : K} (hz : z ≠ 0)
    (h1 : z ∈ W) (h2 : z⁻¹ ∈ W) : W.valuation z = 1 := by
  have hu : IsUnit (⟨z, h1⟩ : W) :=
    ⟨⟨⟨z, h1⟩, ⟨z⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hz), Subtype.ext (inv_mul_cancel₀ hz)⟩, rfl⟩
  exact (W.valuation_eq_one_iff ⟨z, h1⟩).1 hu

private theorem aeval_jK_mem_of_overY {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (V : ValuationSubring X.K) (hV : X.OverY V) (P : Polynomial Ω) : Polynomial.aeval X.jK P ∈ V := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact mul_mem (hV.1 c) (pow_mem hV.2 n)

private theorem inv_aeval_mem_of_inv_sub_not_mem_of_eval_ne_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (V : ValuationSubring X.K) (hV : X.OverY V) (c : Ω)
    (hc : (X.jK - algebraMap Ω X.K c)⁻¹ ∉ V) (R : Polynomial Ω) (hR : R.eval c ≠ 0) :
    (Polynomial.aeval X.jK R)⁻¹ ∈ V := by
  set t := X.jK - algebraMap Ω X.K c with ht
  have htV : t ∈ V := sub_mem hV.2 (hV.1 c)
  have hvt : V.valuation t < 1 := by
    rcases lt_or_eq_of_le ((V.valuation_le_one_iff t).2 htV) with h | h
    · exact h
    · exfalso
      apply hc
      rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]
  have hdiv : (Polynomial.X - Polynomial.C c) * ((R - Polynomial.C (R.eval c)) /ₘ (Polynomial.X - Polynomial.C c))
      = R - Polynomial.C (R.eval c) := by
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
    simp
  have hR' : Polynomial.aeval X.jK R = algebraMap Ω X.K (R.eval c)
      + t * Polynomial.aeval X.jK ((R - Polynomial.C (R.eval c)) /ₘ (Polynomial.X - Polynomial.C c)) := by
    have h := congrArg (Polynomial.aeval X.jK) hdiv
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    linear_combination (-1 : X.K) * h
  have hcst : V.valuation (algebraMap Ω X.K (R.eval c)) = 1 := by
    apply valuation_eq_one_of_mem_of_inv_mem V ((map_ne_zero (algebraMap Ω X.K)).2 hR) (hV.1 _)
    rw [← map_inv₀]
    exact hV.1 _
  have hsmall : V.valuation (t * Polynomial.aeval X.jK
      ((R - Polynomial.C (R.eval c)) /ₘ (Polynomial.X - Polynomial.C c))) < 1 := by
    rw [map_mul]
    calc _ ≤ V.valuation t * 1 :=
          mul_le_mul' (le_refl _) ((V.valuation_le_one_iff _).2 (aeval_jK_mem_of_overY X V hV _))
      _ < 1 := by rw [mul_one]; exact hvt
  have hval : V.valuation (Polynomial.aeval X.jK R) = 1 := by
    rw [hR', Valuation.map_add_eq_of_lt_left _ (by rw [hcst]; exact hsmall), hcst]
  rw [← V.valuation_le_one_iff, map_inv₀, hval, inv_one]

private theorem aeval_div_mem_of_mem_of_same_pole {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (V1 V2 : ValuationSubring X.K) (hV1 : X.OverY V1) (hV2 : X.OverY V2) (c : Ω)
    (h1 : (X.jK - algebraMap Ω X.K c)⁻¹ ∉ V1) (h2 : (X.jK - algebraMap Ω X.K c)⁻¹ ∉ V2)
    (P Q : Polynomial Ω) (hPQ : Polynomial.aeval X.jK P / Polynomial.aeval X.jK Q ∈ V1) :
    Polynomial.aeval X.jK P / Polynomial.aeval X.jK Q ∈ V2 := by
  have htne : X.jK - algebraMap Ω X.K c ≠ 0 := by
    intro h0
    apply h1
    rw [h0, inv_zero]
    exact zero_mem _
  by_cases hP0 : Polynomial.aeval X.jK P = 0
  · rw [hP0, zero_div]
    exact zero_mem _
  by_cases hQ0 : Polynomial.aeval X.jK Q = 0
  · rw [hQ0, div_zero]
    exact zero_mem _
  have hP : P ≠ 0 := by
    rintro rfl
    exact hP0 (map_zero _)
  have hQ : Q ≠ 0 := by
    rintro rfl
    exact hQ0 (map_zero _)
  obtain ⟨P', hPe, hP'⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP c
  obtain ⟨Q', hQe, hQ'⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ c
  rw [Polynomial.dvd_iff_isRoot] at hP' hQ'
  have hPa : Polynomial.aeval X.jK P = (X.jK - algebraMap Ω X.K c) ^ Polynomial.rootMultiplicity c P
      * Polynomial.aeval X.jK P' := by
    conv_lhs => rw [hPe]
    simp only [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  have hQa : Polynomial.aeval X.jK Q = (X.jK - algebraMap Ω X.K c) ^ Polynomial.rootMultiplicity c Q
      * Polynomial.aeval X.jK Q' := by
    conv_lhs => rw [hQe]
    simp only [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  have hP'ne : Polynomial.aeval X.jK P' ≠ 0 := by
    intro h
    apply hP0
    rw [hPa, h, mul_zero]
  have hQ'ne : Polynomial.aeval X.jK Q' ≠ 0 := by
    intro h
    apply hQ0
    rw [hQa, h, mul_zero]
  rw [hPa, hQa] at hPQ ⊢
  generalize Polynomial.rootMultiplicity c P = p at hPQ ⊢
  generalize Polynomial.rootMultiplicity c Q = q at hPQ ⊢
  generalize hT : X.jK - algebraMap Ω X.K c = t at hPQ htne h1 h2 ⊢
  have htV1 : t ∈ V1 := hT ▸ sub_mem hV1.2 (hV1.1 c)
  have htV2 : t ∈ V2 := hT ▸ sub_mem hV2.2 (hV2.1 c)
  rcases le_or_gt q p with hqp | hpq
  · obtain ⟨d, rfl⟩ : ∃ d, p = q + d := ⟨p - q, by omega⟩
    have heq : t ^ (q + d) * Polynomial.aeval X.jK P' / (t ^ q * Polynomial.aeval X.jK Q')
        = t ^ d * Polynomial.aeval X.jK P' * (Polynomial.aeval X.jK Q')⁻¹ := by
      rw [pow_add]
      field_simp
    rw [heq]
    exact mul_mem (mul_mem (pow_mem htV2 _) (aeval_jK_mem_of_overY X V2 hV2 P'))
      (inv_aeval_mem_of_inv_sub_not_mem_of_eval_ne_zero X V2 hV2 c (by rw [hT]; exact h2) Q' hQ')
  · exfalso
    apply h1
    obtain ⟨d, rfl⟩ : ∃ d, q = p + d + 1 := ⟨q - p - 1, by omega⟩
    have heq : t⁻¹ = (t ^ p * Polynomial.aeval X.jK P' / (t ^ (p + d + 1) * Polynomial.aeval X.jK Q'))
        * Polynomial.aeval X.jK Q' * (Polynomial.aeval X.jK P')⁻¹ * t ^ d := by
      rw [pow_add, pow_add]
      field_simp
    rw [heq]
    exact mul_mem (mul_mem (mul_mem hPQ (aeval_jK_mem_of_overY X V1 hV1 Q'))
      (inv_aeval_mem_of_inv_sub_not_mem_of_eval_ne_zero X V1 hV1 c (by rw [hT]; exact h1) P' hP')) (pow_mem htV1 _)

private theorem aeval_div_mem_of_forall_inv_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (V : ValuationSubring X.K) (hV : X.OverY V) (h : ∀ c : Ω, (X.jK - algebraMap Ω X.K c)⁻¹ ∈ V)
    (P Q : Polynomial Ω) : Polynomial.aeval X.jK P / Polynomial.aeval X.jK Q ∈ V := by
  have key : ∀ n : ℕ, ∀ Q : Polynomial Ω, Q.natDegree = n → (Polynomial.aeval X.jK Q)⁻¹ ∈ V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Q hQn
      by_cases hQ0 : Q = 0
      · rw [hQ0, map_zero, inv_zero]
        exact zero_mem _
      by_cases hdeg : Q.degree = 0
      · rw [Polynomial.eq_C_of_degree_eq_zero hdeg, Polynomial.aeval_C, ← map_inv₀]
        exact hV.1 _
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root Q hdeg
      have hdiv := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hr
      have hpos : 0 < Q.natDegree :=
        Polynomial.natDegree_pos_iff_degree_pos.2
          (lt_of_le_of_ne (Polynomial.zero_le_degree_iff.2 hQ0) (Ne.symm hdeg))
      have hlt : (Q /ₘ (Polynomial.X - Polynomial.C r)).natDegree < n := by
        rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C r), Polynomial.natDegree_X_sub_C]
        omega
      rw [← hdiv, map_mul, mul_inv, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      exact mul_mem (h r) (ih _ hlt _ rfl)
  rw [div_eq_mul_inv]
  exact mul_mem (aeval_jK_mem_of_overY X V hV P) (key _ Q rfl)

private theorem mem_and_inv_mem_of_analyticOrderAt_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ Hs) (W : ValuationSubring X.K)
    (hW : ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ)
    (z : X.K) (hz : z ≠ 0) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hab : X.an z * (b : Mero) = (a : Mero)) (hord : analyticOrderAt a τ = analyticOrderAt b τ)
    (hfin : analyticOrderAt b τ ≠ ⊤) : z ∈ W ∧ z⁻¹ ∈ W := by
  have key : ∀ (w : X.K) (a b : ℂ → ℂ), DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs →
      X.an w * (b : Mero) = (a : Mero) → analyticOrderAt a τ = analyticOrderAt b τ →
      analyticOrderAt b τ ≠ ⊤ → w ∈ W := by
    intro w a b ha hb hab hord hfin
    rw [hW]
    refine H3.exists_analyticAt_of_order_nonneg X hτ w a b ha hb (mero_coe_ne_zero_of_analyticOrderAt_finite hτ hb hfin) hab ?_
    have ha' : AnalyticAt ℂ a τ := (ha.analyticOnNhd H3.isOpen_Hs_place) τ hτ
    have hb' : AnalyticAt ℂ b τ := (hb.analyticOnNhd H3.isOpen_Hs_place) τ hτ
    rw [div_eq_mul_inv, meromorphicOrderAt_mul ha'.meromorphicAt hb'.meromorphicAt.inv,
      meromorphicOrderAt_inv, ha'.meromorphicOrderAt_eq, hb'.meromorphicOrderAt_eq, hord]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin
    rw [← hn]
    simp
  refine ⟨key z a b ha hb hab hord hfin, key z⁻¹ b a hb ha ?_ hord.symm (by rw [hord]; exact hfin)⟩
  calc X.an z⁻¹ * (a : Mero) = X.an z⁻¹ * (X.an z * (b : Mero)) := by rw [hab]
    _ = (b : Mero) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hz, map_one, one_mul]

private theorem mem_and_inv_mem_of_pow_div_pow_of_orders {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ Hs) (W : ValuationSubring X.K)
    (hW : ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ)
    (xs t : X.K) (hxs : xs ≠ 0) (ht : t ≠ 0) (a1 b1 g : ℂ → ℂ) (ha1 : DifferentiableOn ℂ a1 Hs)
    (hb1 : DifferentiableOn ℂ b1 Hs) (hg : DifferentiableOn ℂ g Hs)
    (hab : X.an xs * (b1 : Mero) = (a1 : Mero)) (htg : X.an t = (g : Mero))
    (E m1 m2 nA nB ne : ℕ) (hA : analyticOrderAt a1 τ = nA) (hB : analyticOrderAt b1 τ = nB)
    (he : analyticOrderAt g τ = ne) (hm : E * nA + m2 * ne = E * nB + m1 * ne) :
    xs ^ E / (t ^ m1 / t ^ m2) ∈ W ∧ (xs ^ E / (t ^ m1 / t ^ m2))⁻¹ ∈ W := by
  have ha1' : AnalyticAt ℂ a1 τ := (ha1.analyticOnNhd H3.isOpen_Hs_place) τ hτ
  have hb1' : AnalyticAt ℂ b1 τ := (hb1.analyticOnNhd H3.isOpen_Hs_place) τ hτ
  have hg' : AnalyticAt ℂ g τ := (hg.analyticOnNhd H3.isOpen_Hs_place) τ hτ
  have hz : xs ^ E / (t ^ m1 / t ^ m2) * t ^ m1 = xs ^ E * t ^ m2 := by
    field_simp
  have hne : xs ^ E / (t ^ m1 / t ^ m2) ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hxs) (div_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ ht))
  have hmain : X.an (xs ^ E / (t ^ m1 / t ^ m2)) * X.an t ^ m1 = X.an xs ^ E * X.an t ^ m2 := by
    rw [← map_pow, ← map_mul, hz, map_mul, map_pow, map_pow]
  apply mem_and_inv_mem_of_analyticOrderAt_eq X hτ W hW _ hne (a1 ^ E * g ^ m2) (b1 ^ E * g ^ m1)
    ((ha1.pow E).mul (hg.pow m2)) ((hb1.pow E).mul (hg.pow m1))
  · simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    rw [← htg, ← hab]
    linear_combination (b1 : Mero) ^ E * hmain
  · rw [analyticOrderAt_mul (ha1'.pow E) (hg'.pow m2), analyticOrderAt_mul (hb1'.pow E) (hg'.pow m1),
      analyticOrderAt_pow ha1', analyticOrderAt_pow hb1', analyticOrderAt_pow hg', analyticOrderAt_pow hg',
      hA, hB, he]
    simp only [nsmul_eq_mul]
    exact_mod_cast hm
  · rw [analyticOrderAt_mul (hb1'.pow E) (hg'.pow m1), analyticOrderAt_pow hb1', analyticOrderAt_pow hg',
      hB, he]
    simp only [nsmul_eq_mul]
    exact_mod_cast ENat.coe_ne_top (E * nB + m1 * ne)

open UpperTheory.Kd.K4.EisensteinBasis in
theorem UpperTheory.Kd.K4.eb :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∃ E : ℕ, 0 < E ∧ ∀ W : ValuationSubring X.K, X.OverY W → ∀ x : X.K, x ≠ 0 → ∃ y ∈ lev X ⊤, y ≠ 0 ∧ W.valuation (x ^ E / y) = 1 := by
  intro Ω _ _ _ ε X
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨φ, E0, hφ, hφd, hsurj, hord⟩ := jan ε X
  have hJ : H3.JHol X := ⟨φ, hφ, hφd⟩
  refine ⟨E0.factorial, Nat.factorial_pos _, ?_⟩
  intro W hW x hx
  obtain ⟨M, hM, hMx⟩ := X.level x
  have hmemlev : ∀ (Γ : Subgroup SL(2, ℤ)) (g : X.K), g ∈ lev X Γ ↔ ∀ δ ∈ Γ, X.sl (ofSL δ) g = g := by
    intro Γ g
    simp [lev, Subfield.mem_iInf, RingHom.mem_eqLocusField]
  have hxL : x ∈ lev X (CongruenceSubgroup.Gamma M) := (hmemlev _ _).2 hMx
  letI := algRat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M)) :=
    GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M hM le_rfl
  haveI : IsGalois (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M)) := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff]
    intro u hu
    rw [IntermediateField.mem_fixedField_iff] at hu
    have hfix : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) (u : X.K) = u := fun γ =>
      congrArg Subtype.val (hu (resA X M γ) (Subgroup.mem_top _))
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff Ω _).1
      (GlobalTheory.T.modularTower_mem_adjoin_j_of_slTwoInt_invariant ε X ⟨φ, hφd, hφ⟩ (u : X.K) hfix)
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap (Polynomial Ω) (RatFunc Ω) r / algebraMap (Polynomial Ω) (RatFunc Ω) s, ?_⟩
    apply Subtype.ext
    rw [hrs]
    exact jRat_coe_div_eq_aeval_div_aeval X _ r s
  have hjRat : ∀ (V : ValuationSubring X.K) (P Q : Polynomial Ω),
      algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M))
        (algebraMap (Polynomial Ω) (RatFunc Ω) P / algebraMap (Polynomial Ω) (RatFunc Ω) Q)
        ∈ V.comap (lev X (CongruenceSubgroup.Gamma M)).subtype ↔
      Polynomial.aeval X.jK P / Polynomial.aeval X.jK Q ∈ V := by
    intro V P Q
    rw [ValuationSubring.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ V) (jRat_coe_div_eq_aeval_div_aeval X _ P Q))
  by_cases hcase : ∃ c : Ω, (X.jK - algebraMap Ω X.K c)⁻¹ ∉ W
  · obtain ⟨c, hc⟩ := hcase
    obtain ⟨τ, hτ, hτc⟩ := hsurj (ε c)
    obtain ⟨Wτ, hWτ, hmem⟩ := H3.exists_place_at_point Ω ε X hJ τ hτ
    have htne : X.jK - algebraMap Ω X.K c ≠ 0 := by
      intro h0
      apply hc
      rw [h0, inv_zero]
      exact zero_mem _
    obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = φ - fun _ => ε c := ⟨_, rfl⟩
    have hgd : DifferentiableOn ℂ g Hs := by
      rw [hg]
      exact hφd.sub (differentiableOn_const _)
    have hg' : AnalyticAt ℂ g τ := (hgd.analyticOnNhd H3.isOpen_Hs_place) τ hτ
    have htg : X.an (X.jK - algebraMap Ω X.K c) = (g : Mero) := by
      rw [map_sub, hφ, X.an_c, hg, Filter.Germ.coe_sub]
    have hgτ : g τ = 0 := by
      rw [hg]
      simp [hτc]
    have hcτ : (X.jK - algebraMap Ω X.K c)⁻¹ ∉ Wτ := by
      rw [hmem]
      rintro ⟨ψ, hψ, hψa⟩
      have h1 : ((g * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero) := by
        rw [Filter.Germ.coe_mul, ← htg, ← hψ, ← map_mul, mul_inv_cancel₀ htne, map_one,
          Filter.Germ.coe_one]
      have h2 := eventually_eq_of_mero_coe_eq hτ h1
      have h3 : Filter.Tendsto (fun y => g y * ψ y) (nhds τ)
          (nhds (g τ * ψ τ)) :=
        (hg'.continuousAt.mul hψa.continuousAt).tendsto
      rw [hgτ, zero_mul] at h3
      have h4 : Filter.Tendsto (fun y => g y * ψ y) (nhdsWithin τ {τ}ᶜ) (nhds 1) :=
        tendsto_const_nhds.congr' (h2.mono fun y hy => by
          simp only [Pi.mul_apply, Pi.one_apply] at hy
          exact hy.symm)
      exact one_ne_zero (tendsto_nhds_unique h4 (h3.mono_left nhdsWithin_le_nhds))
    have hres : ∀ a : RatFunc Ω,
        algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M)) a
          ∈ W.comap (lev X (CongruenceSubgroup.Gamma M)).subtype ↔
        algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M)) a
          ∈ Wτ.comap (lev X (CongruenceSubgroup.Gamma M)).subtype := by
      intro a
      rw [← RatFunc.num_div_denom a, hjRat, hjRat]
      exact ⟨aeval_div_mem_of_mem_of_same_pole X W Wτ hW hWτ c hc hcτ _ _, aeval_div_mem_of_mem_of_same_pole X Wτ W hWτ hW c hcτ hc _ _⟩
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M))
      (W.comap (lev X (CongruenceSubgroup.Gamma M)).subtype)
      (Wτ.comap (lev X (CongruenceSubgroup.Gamma M)).subtype) hres
    have hxs : ((σ ⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) : X.K) ≠ 0 := by
      intro h0
      have h1 : σ ⟨x, hxL⟩ = 0 := Subtype.ext h0
      exact hx (congrArg Subtype.val ((map_eq_zero_iff σ σ.injective).1 h1))
    obtain ⟨a1, b1, ha1, hb1, hb1ne, hab⟩ :=
      X.an_mero ((σ ⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) : X.K)
    have ha1ne : (a1 : Mero) ≠ 0 := by
      intro h0
      apply hb1ne
      have h1 : X.an ((σ ⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) : X.K)⁻¹
          * (X.an ((σ ⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) : X.K) * (b1 : Mero)) = b1 := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hxs, map_one, one_mul]
      rw [← h1, hab, h0, mul_zero]
    obtain ⟨nA, hA⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_finite_of_mero_ne_zero hτ ha1 ha1ne)
    obtain ⟨nB, hB⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_finite_of_mero_ne_zero hτ hb1 hb1ne)
    have hgle : analyticOrderAt g τ ≤ E0 := by
      have h := hord τ hτ
      have h' : (fun s => φ s - φ τ) = g := by
        rw [hg]
        funext s
        simp [hτc]
      rwa [h'] at h
    obtain ⟨ne, he⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top E0) hgle)
    have hne0 : ne ≠ 0 := by
      intro h0
      apply (hg'.analyticOrderAt_eq_zero).1 (by rw [← he, h0, Nat.cast_zero])
      exact hgτ
    have hnele : ne ≤ E0 := by
      rw [← he] at hgle
      exact_mod_cast hgle
    have hdvd : ne ∣ E0.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hne0) hnele
    obtain ⟨m1, m2, hm⟩ : ∃ m1 m2 : ℕ, E0.factorial * nA + m2 * ne = E0.factorial * nB + m1 * ne := by
      rcases le_total nB nA with h | h
      · refine ⟨E0.factorial * (nA - nB) / ne, 0, ?_⟩
        rw [Nat.div_mul_cancel (dvd_mul_of_dvd_left hdvd _), Nat.mul_sub, zero_mul, add_zero]
        have := Nat.mul_le_mul_left E0.factorial h
        omega
      · refine ⟨0, E0.factorial * (nB - nA) / ne, ?_⟩
        rw [Nat.div_mul_cancel (dvd_mul_of_dvd_left hdvd _), Nat.mul_sub, zero_mul, add_zero]
        have := Nat.mul_le_mul_left E0.factorial h
        omega
    have htlev : X.jK - algebraMap Ω X.K c ∈ lev X ⊤ := by
      rw [hmemlev]
      intro δ _
      rw [map_sub, X.j_inv, AlgEquiv.commutes]
    refine ⟨(X.jK - algebraMap Ω X.K c) ^ m1 / (X.jK - algebraMap Ω X.K c) ^ m2,
      div_mem (pow_mem htlev _) (pow_mem htlev _),
      div_ne_zero (pow_ne_zero _ htne) (pow_ne_zero _ htne), ?_⟩
    have hrYv : ((algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M))
        (algebraMap (Polynomial Ω) (RatFunc Ω) ((Polynomial.X - Polynomial.C c) ^ m1)
          / algebraMap (Polynomial Ω) (RatFunc Ω) ((Polynomial.X - Polynomial.C c) ^ m2))
        : lev X (CongruenceSubgroup.Gamma M)) : X.K)
        = (X.jK - algebraMap Ω X.K c) ^ m1 / (X.jK - algebraMap Ω X.K c) ^ m2 := by
      have h := jRat_coe_div_eq_aeval_div_aeval X (CongruenceSubgroup.Gamma M) ((Polynomial.X - Polynomial.C c) ^ m1)
        ((Polynomial.X - Polynomial.C c) ^ m2)
      refine h.trans ?_
      simp only [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    obtain ⟨hz1, hz2⟩ := mem_and_inv_mem_of_pow_div_pow_of_orders X hτ Wτ hmem _ _ hxs htne a1 b1 _ ha1 hb1 hgd hab htg
      E0.factorial m1 m2 nA nB ne hA.symm hB.symm he.symm hm
    obtain ⟨u, hu⟩ : ∃ u : lev X (CongruenceSubgroup.Gamma M), u = (⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) ^ E0.factorial /
        algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M))
        (algebraMap (Polynomial Ω) (RatFunc Ω) ((Polynomial.X - Polynomial.C c) ^ m1)
          / algebraMap (Polynomial Ω) (RatFunc Ω) ((Polynomial.X - Polynomial.C c) ^ m2)) := ⟨_, rfl⟩
    have huv : (u : X.K)
        = x ^ E0.factorial / ((X.jK - algebraMap Ω X.K c) ^ m1 / (X.jK - algebraMap Ω X.K c) ^ m2) := by
      rw [hu, Subfield.coe_div, SubmonoidClass.coe_pow, hrYv]
    have hσu : ((σ u : lev X (CongruenceSubgroup.Gamma M)) : X.K)
        = ((σ ⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) : X.K) ^ E0.factorial
          / ((X.jK - algebraMap Ω X.K c) ^ m1 / (X.jK - algebraMap Ω X.K c) ^ m2) := by
      rw [hu, map_div₀, map_pow, AlgEquiv.commutes, Subfield.coe_div, SubmonoidClass.coe_pow, hrYv]
    apply valuation_eq_one_of_mem_of_inv_mem W (div_ne_zero (pow_ne_zero _ hx) (div_ne_zero (pow_ne_zero _ htne) (pow_ne_zero _ htne)))
    · rw [← huv]
      have h0 : ((σ u : lev X (CongruenceSubgroup.Gamma M)) : X.K) ∈ Wτ := by
        rw [hσu]
        exact hz1
      exact ValuationSubring.mem_comap.1 ((hσ u).1 (ValuationSubring.mem_comap.2 h0))
    · rw [← huv, ← Subfield.coe_inv]
      have h0 : ((σ u⁻¹ : lev X (CongruenceSubgroup.Gamma M)) : X.K) ∈ Wτ := by
        rw [map_inv₀, Subfield.coe_inv, hσu]
        exact hz2
      exact ValuationSubring.mem_comap.1 ((hσ u⁻¹).1 (ValuationSubring.mem_comap.2 h0))
  · push_neg at hcase
    have hall : ∀ a : RatFunc Ω,
        algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M)) a
          ∈ W.comap (lev X (CongruenceSubgroup.Gamma M)).subtype ↔
        algebraMap (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M)) a
          ∈ (⊤ : ValuationSubring (lev X (CongruenceSubgroup.Gamma M))) := by
      intro a
      rw [← RatFunc.num_div_denom a, hjRat]
      exact ⟨fun _ => ValuationSubring.mem_top _, fun _ => aeval_div_mem_of_forall_inv_sub_mem X W hW hcase _ _⟩
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_galois_conj_valuationSubring_same_trace (RatFunc Ω) (lev X (CongruenceSubgroup.Gamma M))
      (W.comap (lev X (CongruenceSubgroup.Gamma M)).subtype) ⊤ hall
    have hallW : ∀ u : lev X (CongruenceSubgroup.Gamma M), (u : X.K) ∈ W := fun u =>
      ValuationSubring.mem_comap.1 ((hσ u).1 (ValuationSubring.mem_top _))
    refine ⟨1, one_mem _, one_ne_zero, ?_⟩
    rw [div_one]
    apply valuation_eq_one_of_mem_of_inv_mem W (pow_ne_zero _ hx)
    · exact hallW ((⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) ^ E0.factorial)
    · exact hallW (((⟨x, hxL⟩ : lev X (CongruenceSubgroup.Gamma M)) ^ E0.factorial)⁻¹)
