import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

section Weight

variable [DecidableEq K]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def mw : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_mw (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (mw (ι := ι)) m = fun k => ∑ i, m ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Finset.sum_apply]
  simp only [Pi.smul_apply, mw, smul_eq_mul]
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, Ne.symm hb]
  · simp

theorem mem_weighted_of_isMultiHomog {f : MRingOver F ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) : f ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) a := by
  rw [mem_weightedHomogeneousSubmodule]
  intro m hm
  rw [weight_mw]
  unfold IsMultiHomog at hf
  have h := hf m (by simpa [MvPolynomial.mem_support_iff] using hm)
  first
    | exact h
    | exact funext h
    | simpa [funext_iff] using h

theorem isMultiHomog_of_mem_weighted {f : MRingOver F ι} {a : K → ℕ}
    (hf : f ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) a) : IsMultiHomog f a := by
  unfold IsMultiHomog
  intro m hm
  rw [mem_weightedHomogeneousSubmodule] at hf
  have h := hf (by simpa [MvPolynomial.mem_support_iff] using hm)
  rw [weight_mw] at h
  first
    | exact h
    | exact congrFun h
    | simpa [funext_iff] using h

theorem monomial_mem_weighted (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    monomial m c ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (fun k => ∑ i, m ⟨k, i⟩) := (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_monomial _ _ _ (weight_mw m))

theorem exists_homog_chart (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (b : MRingOver F ι) :
    ∃ e₀ : K → ℕ, ∀ e, e₀ ≤ e → ∃ b' ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e,
      Ideal.Quotient.mk (chartIdeal V j) b' = Ideal.Quotient.mk (chartIdeal V j) b := by
  have hX1 : ∀ k, Ideal.Quotient.mk (chartIdeal V j) (X ⟨k, j k⟩) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk (chartIdeal V j)), Ideal.Quotient.eq]
    unfold chartIdeal
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨fun _ => b.totalDegree, fun e he => ?_⟩
  have hd : ∀ m ∈ b.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ e k := by
    intro m hm k
    calc ∑ i, m ⟨k, i⟩ ≤ ∑ k', ∑ i, m ⟨k', i⟩ :=
          Finset.single_le_sum (f := fun k' => ∑ i, m ⟨k', i⟩) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ k)
      _ = m.sum fun _ n => n := by rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
      _ ≤ b.totalDegree := MvPolynomial.le_totalDegree hm
      _ ≤ e k := he k
  refine ⟨∑ m ∈ b.support, monomial m (coeff m b) * ∏ k, X ⟨k, j k⟩ ^ (e k - ∑ i, m ⟨k, i⟩),
    ?_, ?_⟩
  · refine Submodule.sum_mem _ fun m hm => ?_
    rw [mem_weightedHomogeneousSubmodule]
    have h1 : IsWeightedHomogeneous (mw (ι := ι)) (monomial m (coeff m b))
        (fun k => ∑ i, m ⟨k, i⟩) :=
      isWeightedHomogeneous_monomial _ _ _ (weight_mw m)
    have h2 : IsWeightedHomogeneous (mw (ι := ι))
        (∏ k, (X ⟨k, j k⟩ : MRingOver F ι) ^ (e k - ∑ i, m ⟨k, i⟩))
        (∑ k, (e k - ∑ i, m ⟨k, i⟩) • mw (ι := ι) ⟨k, j k⟩) :=
      IsWeightedHomogeneous.prod _ _ _ fun k _ =>
        (isWeightedHomogeneous_X (R := F) (w := mw (ι := ι)) (i := (⟨k, j k⟩ : Σ k, ι k))).pow _
    have h3 := h1.mul h2
    have hsum : ((fun k => ∑ i, m ⟨k, i⟩) +
        ∑ k, (e k - ∑ i, m ⟨k, i⟩) • mw (ι := ι) ⟨k, j k⟩) = e := by
      funext k
      have := hd m hm k
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, mw, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      omega
    rwa [hsum] at h3
  · rw [map_sum]
    conv_rhs => rw [MvPolynomial.as_sum b, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_prod]
    simp only [map_pow, hX1, one_pow, Finset.prod_const_one, mul_one]

end Weight

section Rho

variable {W : Ideal (MRingOver F ι)} [hWp : W.IsPrime]

def chartTheta (W : Ideal (MRingOver F ι)) [W.IsPrime] :
    MRingOver F ι →ₐ[F] FractionRing (MRingOver F ι ⧸ W) :=
  (IsScalarTower.toAlgHom F (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))).comp
    (Ideal.Quotient.mkₐ F W)

theorem chartTheta_apply (g : MRingOver F ι) :
    chartTheta W g = algebraMap (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))
      (Ideal.Quotient.mk W g) := rfl

theorem chartTheta_eq_zero_iff {g : MRingOver F ι} : chartTheta W g = 0 ↔ g ∈ W := by
  rw [chartTheta_apply, map_eq_zero_iff _
    (IsFractionRing.injective (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))),
    Ideal.Quotient.eq_zero_iff_mem]

def chartC (W : Ideal (MRingOver F ι)) [W.IsPrime] (j : ∀ k, ι k) (k : K) :
    FractionRing (MRingOver F ι ⧸ W) :=
  (chartTheta W (X ⟨k, j k⟩))⁻¹

def chartRho (W : Ideal (MRingOver F ι)) [W.IsPrime] (j : ∀ k, ι k) :
    MRingOver F ι →ₐ[F] FractionRing (MRingOver F ι ⧸ W) :=
  aeval fun p => chartC W j p.1 * chartTheta W (X p)

theorem chartTheta_X_ne_zero {j : ∀ k, ι k} (hj : IsChart W j) (k : K) :
    chartTheta W (X ⟨k, j k⟩) ≠ 0 := by
  rw [Ne, chartTheta_eq_zero_iff]
  unfold IsChart at hj
  exact hj k

private theorem aeval_mul_const_of_isMultiHomog {A : Type*} [CommRing A] [Algebra F A] (c : K → A)
    (y : (Σ k, ι k) → A) {f : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    aeval (fun p => c p.1 * y p) f = (∏ k, c k ^ a k) * aeval y f := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).mp (mem_weighted_of_isMultiHomog hf)
    (MvPolynomial.mem_support_iff.mp hm)
  rw [weight_mw] at hw
  rw [aeval_monomial, aeval_monomial]
  have key : (m.prod fun p e => c p.1 ^ e) = ∏ k, c k ^ a k := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma, ← hw]
    simp only [Finset.prod_pow_eq_pow_sum]
  have split : (m.prod fun p e => (c p.1 * y p) ^ e) =
      (m.prod fun p e => c p.1 ^ e) * m.prod fun p e => y p ^ e := by
    simp only [mul_pow]
    exact Finsupp.prod_mul
  rw [split, key]
  ring

theorem chartRho_chartIdeal (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k} (hj : IsChart W j)
    {g : MRingOver F ι} (hg : g ∈ chartIdeal W j) : chartRho W j g = 0 := by
  have hX : ∀ k, chartRho W j (X ⟨k, j k⟩ - 1) = 0 := by
    intro k
    rw [map_sub, map_one]
    unfold chartRho chartC
    rw [aeval_X, inv_mul_cancel₀ (chartTheta_X_ne_zero hj k), sub_self]
  obtain ⟨S, hS, hWS⟩ := hW
  have hS0 : Ideal.span S ≤ RingHom.ker (chartRho W j) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have hfW : f ∈ W := by
      rw [hWS]
      exact Ideal.subset_span hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 := aeval_mul_const_of_isMultiHomog (chartC W j) (fun p => chartTheta W (X p)) ha
    have h2 : aeval (fun p => chartTheta W (X p)) f = chartTheta W f :=
      (DFunLike.congr_fun (MvPolynomial.aeval_unique (chartTheta W)) f).symm
    have h3 : chartRho W j f = (∏ k, chartC W j k ^ a k) * chartTheta W f := by
      rw [← h2, ← h1]
      rfl
    rw [h3, chartTheta_eq_zero_iff.mpr hfW, mul_zero]
  have hker : chartIdeal W j ≤ RingHom.ker (chartRho W j) := by
    unfold chartIdeal
    refine sup_le (hWS.le.trans hS0) ?_
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact RingHom.mem_ker.mpr (hX k)
  exact RingHom.mem_ker.mp (hker hg)

theorem chartRho_form [DecidableEq K] {j : ∀ k, ι k} (hj : IsChart W j) {e : K → ℕ} {a : MRingOver F ι}
    (ha : a ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e) (h0 : chartRho W j a = 0) : a ∈ W := by
  have h1 := aeval_mul_const_of_isMultiHomog (chartC W j) (fun p => chartTheta W (X p))
    (isMultiHomog_of_mem_weighted ha)
  have h2 : aeval (fun p => chartTheta W (X p)) a = chartTheta W a :=
    (DFunLike.congr_fun (MvPolynomial.aeval_unique (chartTheta W)) a).symm
  have h3 : chartRho W j a = (∏ k, chartC W j k ^ e k) * chartTheta W a := by
    rw [← h2, ← h1]
    rfl
  rw [h3] at h0
  have hne : (∏ k, chartC W j k ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (chartTheta_X_ne_zero hj k))
  exact chartTheta_eq_zero_iff.mp ((mul_eq_zero.mp h0).resolve_left hne)

theorem mem_of_mem_chartIdeal [DecidableEq K] (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k}
    (hj : IsChart W j) {e : K → ℕ} {a : MRingOver F ι}
    (ha : a ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e) (haW : a ∈ chartIdeal W j) : a ∈ W := chartRho_form hj ha (chartRho_chartIdeal hW hj haW)

theorem chartIdeal_ne_top (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k} (hj : IsChart W j) :
    chartIdeal W j ≠ ⊤ := by
  intro h
  have h1 := chartRho_chartIdeal hW hj ((Ideal.eq_top_iff_one _).mp h)
  rw [map_one] at h1
  exact one_ne_zero h1

end Rho

section Point

variable {W : Ideal (MRingOver F ι)}

theorem isUnit_mk_chartIdeal_form {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) (j : ∀ k, ι k)
    {a : MRingOver F ι} {α : K → ℕ} (ha : IsMultiHomog a α) (hp : a ∉ V) :
    IsUnit (Ideal.Quotient.mk (chartIdeal V j) a) := by
  classical
  by_contra hu
  obtain ⟨M, hM, hpM⟩ := exists_max_ideal_of_mem_nonunits hu
  have hVp : V.IsPrime := hV.1.1
  letI : Field (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) := Ideal.Quotient.field M
  let θ : MRingOver F ι →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    (IsScalarTower.toAlgHom F (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) (MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)))).comp
      ((Ideal.Quotient.mkₐ F M).comp (Ideal.Quotient.mkₐ F (chartIdeal V j)))
  have hθ : ∀ g, θ g = MvPolynomial.C (Ideal.Quotient.mk M (Ideal.Quotient.mk (chartIdeal V j) g)) := fun g => rfl
  let c : Finset K → K → MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    fun S k => if k ∈ S then 0 else MvPolynomial.X k
  let φ : Finset K → MRingOver F ι →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    fun S => aeval fun q => c S q.1 * θ (X q)
  have hφX : ∀ S q, φ S (X q) = c S q.1 * θ (X q) := fun S q => aeval_X _ _
  let Q : Finset K → Ideal (MRingOver F ι) := fun S => RingHom.ker (φ S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => RingHom.ker_isPrime (φ S).toRingHom
  have hVQ : ∀ S, V ≤ Q S := fun S g hg => RingHom.mem_ker.mpr
    (aeval_blockScale_eq_zero hV.1.2.1 (c S) θ (fun g hg => by
      rw [hθ, Ideal.Quotient.eq_zero_iff_mem.mpr (show g ∈ chartIdeal V j from Ideal.mem_sup_left hg),
        map_zero, map_zero]) hg)

  have hmono : ∀ S k, Q S ≤ Q (insert k S) := by
    intro S k g hg
    let ρ : MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
      (aeval fun k' => if k' = k then 0 else MvPolynomial.X k').restrictScalars F
    have e : ρ.comp (φ S) = φ (insert k S) := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, hφX, hφX, map_mul]
      congr 1
      · by_cases h1 : q.1 ∈ S
        · simp [ρ, c, h1]
        · by_cases h2 : q.1 = k
          · subst h2
            simp [ρ, c, h1]
          · simp [ρ, c, h1, h2]
      · rw [hθ]
        simp [ρ, MvPolynomial.algebraMap_eq]
    have hg' : φ S g = 0 := RingHom.mem_ker.mp hg
    show φ (insert k S) g = 0
    rw [← e, AlgHom.comp_apply, hg', map_zero]
  have hin : ∀ S k, (X ⟨k, j k⟩ : MRingOver F ι) ∈ Q (insert k S) := by
    intro S k
    show φ (insert k S) (X ⟨k, j k⟩) = 0
    rw [hφX]
    simp [c]
  have hout : ∀ S k, k ∉ S → (X ⟨k, j k⟩ : MRingOver F ι) ∉ Q S := by
    intro S k hk h
    have h' : φ S (X ⟨k, j k⟩) = 0 := RingHom.mem_ker.mp h
    rw [hφX, hθ, mk_chartIdeal_X_self, map_one, map_one, mul_one] at h'
    simp only [c, if_neg hk] at h'
    exact MvPolynomial.X_ne_zero k h'
  have hbase : a ∈ Q ∅ := by
    show φ ∅ a = 0
    have e1 := aeval_blockScale ha (c ∅) (fun q => θ (X q))
    have e2 : (aeval fun q => θ (X q) : MRingOver F ι →ₐ[F] _) = θ :=
      MvPolynomial.algHom_ext fun q => aeval_X _ _
    rw [DFunLike.congr_fun e2 a, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero,
      mul_zero] at e1
    exact e1
  have chain : ∀ S : Finset K, ((S.card : ℕ) : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q S) ≤
      ringKrullDim (MRingOver F ι ⧸ V) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have := cyc_dim_add_one_le (hVQ ∅) hbase hp
      rw [Finset.card_empty, Nat.cast_zero, zero_add, add_comm]
      exact this
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have h1 := cyc_dim_add_one_le (hmono S k) (hin S k) (hout S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + 1 + (ringKrullDim (MRingOver F ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q S) := add_le_add_right h1 _
        _ ≤ _ := ih
  have h := chain Finset.univ
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRingOver F ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRingOver F ι ⧸ Q Finset.univ) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hV.2, Finset.card_univ] at h
  have h2 : (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 1 + 0 := by
          push_cast; simp
      _ ≤ _ := add_le_add_right h0 _
      _ ≤ _ := h
  have h3 : Fintype.card K + 1 ≤ 0 + Fintype.card K := by exact_mod_cast h2
  omega

theorem chart_isField (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    IsField (MRingOver F ι ⧸ chartIdeal W j) := by
  classical
  haveI := hW.1.1
  have hnt : Nontrivial (MRingOver F ι ⧸ chartIdeal W j) :=
    Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hW.1.2.1 hj)
  refine ⟨exists_pair_ne _, mul_comm, fun {y} hy => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨e₀, h⟩ := exists_homog_chart W j b
  obtain ⟨b', hb', eb⟩ := h e₀ le_rfl
  have hb'W : b' ∉ W := fun h => hy (by
    rw [← eb]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left h))
  have hu := isUnit_mk_chartIdeal_form hW j (isMultiHomog_of_mem_weighted hb') hb'W
  rw [eb] at hu
  exact hu.exists_right_inv

theorem chart_finite (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    Module.Finite F (MRingOver F ι ⧸ chartIdeal W j) := by
  letI := (chart_isField hW hj).toField
  haveI : Algebra.FiniteType F (MRingOver F ι ⧸ chartIdeal W j) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F (chartIdeal W j))
      (Ideal.Quotient.mkₐ_surjective F _)
  exact finite_of_finite_type_of_isJacobsonRing F _

instance finiteDimensional_weighted [DecidableEq K] (e : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (mw (ι := ι)) e) := by
  classical
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single]
  apply FiniteDimensional.span_of_finite
  have hfin : {m : (Σ k, ι k) →₀ ℕ | Finsupp.weight (mw (ι := ι)) m = e}.Finite := by
    apply (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun p : Σ k, ι k => e p.1)).subset
    intro m hm
    rw [Set.mem_setOf_eq, weight_mw] at hm
    rw [Set.mem_Iic, Finsupp.le_def]
    intro p
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← hm]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p.2)
  exact hfin.image _

theorem point_hilb [DecidableEq K] (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    ∃ e₀ : K → ℕ, ∀ e, e₀ ≤ e →
      Module.finrank F ↥(weightedHomogeneousSubmodule F (mw (ι := ι)) e ⊓ W.restrictScalars F) +
        ptDeg W j = Module.finrank F ↥(weightedHomogeneousSubmodule F (mw (ι := ι)) e) := by
  haveI := chart_finite hW hj
  haveI := hW.1.1
  let bs := Module.finBasis F (MRingOver F ι ⧸ chartIdeal W j)
  choose lift hlift using fun i => Ideal.Quotient.mk_surjective (bs i)
  choose e0 he0 using fun i => exists_homog_chart W j (lift i)
  refine ⟨Finset.univ.sup e0, fun e he => ?_⟩
  let π : weightedHomogeneousSubmodule F (mw (ι := ι)) e →ₗ[F] MRingOver F ι ⧸ chartIdeal W j :=
    (Ideal.Quotient.mkₐ F (chartIdeal W j)).toLinearMap ∘ₗ Submodule.subtype _
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← bs.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨b', hb', eb⟩ := he0 i e ((Finset.le_sup (Finset.mem_univ i)).trans he)
    exact ⟨⟨b', hb'⟩, by simp [π, eb, hlift]⟩
  have hker : LinearMap.ker π = (W.restrictScalars F).comap (Submodule.subtype _) := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem,
      Submodule.coe_subtype]
    constructor
    · intro h
      exact mem_of_mem_chartIdeal hW.1.2.1 hj x.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    · intro h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left h)
  have h1 := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype] at h1
  rw [ptDeg]
  omega

theorem eq_of_point_le {P : Ideal (MRingOver F ι)} (hW : IsProjVarF W 0) (hP : P.IsPrime)
    (hPh : IsMultiHomogIdeal P) {j : ∀ k, ι k} (hj : IsChart P j) (hWP : W ≤ P) : P = W := by
  classical
  refine le_antisymm ?_ hWP
  intro x hxP
  by_contra hxW
  obtain ⟨S, hS, hPS⟩ := hPh
  have hex : ∃ s ∈ S, s ∉ W := by
    by_contra! h
    exact hxW ((hPS ▸ Ideal.span_le.mpr h : P ≤ W) hxP)
  obtain ⟨s, hsS, hsW⟩ := hex
  obtain ⟨a, ha⟩ := hS s hsS
  have hsP : s ∈ P := hPS ▸ Ideal.subset_span hsS
  obtain ⟨t, ht⟩ := (isUnit_mk_chartIdeal_form hW j ha hsW).exists_right_inv
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  have h1 : s * t - 1 ∈ chartIdeal W j := by
    rw [← Ideal.Quotient.eq, map_mul, ht, map_one]
  have h2 : chartIdeal W j ≤ chartIdeal P j := sup_le_sup_right hWP _
  have h3 : s * t ∈ chartIdeal P j := Ideal.mem_sup_left (P.mul_mem_right t hsP)
  have h4 : (1 : MRingOver F ι) ∈ chartIdeal P j := by
    have := Ideal.sub_mem _ h3 (h2 h1)
    simpa using this
  haveI := hP
  exact chartIdeal_ne_top (W := P) ⟨S, hS, hPS⟩ hj ((Ideal.eq_top_iff_one _).mpr h4)

end Point

end ReciprocityTheory.ChartRestriction.G.AI.I1
