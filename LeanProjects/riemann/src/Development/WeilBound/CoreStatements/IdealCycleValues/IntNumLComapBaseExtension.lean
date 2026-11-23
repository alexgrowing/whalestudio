import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace BaseChangeColon.PlField

section Eventual

variable {K : Type}

theorem foldr_eventually (c : ℤ) (L : List (K → ℤ)) {f g : (K → ℤ) → ℤ}
    (h : ∀ᶠ m in Filter.atTop, f m = c * g m) :
    ∀ᶠ m in Filter.atTop, L.foldr diffStep f m = c * L.foldr diffStep g m := by
  induction L with
  | nil => simpa using h
  | cons b L ih =>
    have ht : Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop := by
      simpa only [sub_eq_add_neg, id] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-b) (Filter.tendsto_id (α := K → ℤ))
    filter_upwards [ih, ht.eventually ih] with m h1 h2
    simp only [List.foldr_cons, diffStep]
    rw [h1, h2, mul_sub]

theorem eventualValue_mul {c : ℤ} (hc : c ≠ 0) {f g : (K → ℤ) → ℤ}
    (h : ∀ᶠ m in Filter.atTop, f m = c * g m) : eventualValue f = c * eventualValue g := by
  by_cases hg : ∃ v, ∀ᶠ m in Filter.atTop, g m = v
  · obtain ⟨v, hv⟩ := hg
    rw [(EventualValueFacts.proof K g v 0).1 hv]
    refine (EventualValueFacts.proof K f (c * v) 0).1 ?_
    filter_upwards [h, hv] with m h1 h2
    rw [h1, h2]
  · have hf : ¬ ∃ v, ∀ᶠ m in Filter.atTop, f m = v := by
      rintro ⟨v, hv⟩
      refine hg ⟨v / c, ?_⟩
      filter_upwards [h, hv] with m h1 h2
      rw [← h2, h1, Int.mul_ediv_cancel_left _ hc]
    rw [eventualValue, eventualValue, dif_neg hg, dif_neg hf, mul_zero]

end Eventual

section Charts

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

noncomputable def ex (c : ∀ k, ι k) (n : ℕ) : (Σ k, ι k) →₀ ℕ := ∑ k, Finsupp.single ⟨k, c k⟩ n

omit [DecidableEq K] in
theorem chart_pow {R : Type} [CommRing R] (c : ∀ k, ι k) (n : ℕ) :
    ((∏ k, X ⟨k, c k⟩) ^ n : MRing ι R) = monomial (ex c n) 1 := by
  rw [ex, monomial_sum_one, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial

theorem weight_ex (c : ∀ k, ι k) (n : ℕ) :
    Finsupp.weight (blockWeight ι) (ex c n) = fun _ => n := by
  funext k
  rw [ex, map_sum, Finset.sum_apply]
  simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, blockWeight, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  simp

theorem ex_le {c : ∀ k, ι k} {n : ℕ} {d : (Σ k, ι k) →₀ ℕ} (h : ∀ k, n ≤ d ⟨k, c k⟩) : ex c n ≤ d := by
  classical
  rintro ⟨k, i⟩
  rw [ex, Finsupp.finsetSum_apply, Finset.sum_eq_single k]
  · rw [Finsupp.single_apply]
    split_ifs with h1
    · rw [← h1]; exact h k
    · exact Nat.zero_le _
  · intro k' _ hk
    rw [Finsupp.single_apply, if_neg]
    intro h1
    exact hk (congrArg Sigma.fst h1)
  · intro h1
    exact absurd (Finset.mem_univ k) h1

variable [∀ k, Fintype (ι k)]

theorem weight_eq_sum (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype d (fun i c => c • blockWeight ι i) (fun _ => zero_smul _ _), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro k' _ hk
    simp [blockWeight, Pi.single_apply, hk, hk.symm]
  · intro h1
    exact absurd (Finset.mem_univ k) h1

theorem exists_chart {n : ℕ} {d : (Σ k, ι k) →₀ ℕ}
    (h : ∀ k, n * Fintype.card (ι k) < Finsupp.weight (blockWeight ι) d k) :
    ∃ c : ∀ k, ι k, ∀ k, n ≤ d ⟨k, c k⟩ := by
  have : ∀ k, ∃ i : ι k, n ≤ d ⟨k, i⟩ := by
    intro k
    by_contra hc
    push Not at hc
    have h1 := h k
    rw [weight_eq_sum] at h1
    have h2 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, n := Finset.sum_le_sum fun i _ => (hc i).le
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at h2
    omega
  choose c hc using this
  exact ⟨c, hc⟩

end Charts

section Fields

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {F F' : Type} [Field F] [Field F'] [Algebra F F'] (V' : Ideal (MRing ι F'))

def Good (n : ℕ) (c : ∀ k, ι k) (a : F') : Prop :=
  ∃ G : MRing ι F, IsMultiHomog G (fun _ => n) ∧
    C a * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') G ∈ V'

variable {V'}

theorem Good.mono {n n' : ℕ} {c : ∀ k, ι k} {a : F'} (h : Good (F := F) V' n c a) (hn : n ≤ n') :
    Good (F := F) V' n' c a := by
  obtain ⟨G, hG, hV⟩ := h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨G * (∏ k, X ⟨k, c k⟩) ^ r, ?_, ?_⟩
  · rw [chart_pow]
    exact IsWeightedHomogeneous.mul hG (isWeightedHomogeneous_monomial _ _ _ (weight_ex c r))
  · have h1 := V'.mul_mem_right ((∏ k, X ⟨k, c k⟩) ^ r) hV
    simp only [map_mul, map_pow, map_prod, map_X]
    convert h1 using 1
    ring

theorem exists_uniform [∀ k, Fintype (ι k)] [FiniteDimensional F F']
    (h : ∀ c a, ∃ n, Good (F := F) V' n c a) : ∃ n, ∀ c a, Good (F := F) V' n c a := by
  classical
  choose nn hnn using h
  let b := Module.finBasis F F'
  let n := Finset.univ.sup fun p : (∀ k, ι k) × Fin (Module.finrank F F') => nn p.1 (b p.2)
  refine ⟨n, fun c a => ?_⟩
  have hb : ∀ i, Good (F := F) V' n c (b i) := fun i =>
    (hnn c (b i)).mono (Finset.le_sup (f := fun p : (∀ k, ι k) × Fin (Module.finrank F F') => nn p.1 (b p.2))
      (Finset.mem_univ (c, i)))
  choose G hG hV using hb
  refine ⟨∑ i, C (b.repr a i) * G i, ?_, ?_⟩
  · exact IsWeightedHomogeneous.sum _ _ _ fun i _ => IsWeightedHomogeneous.C_mul (hG i) _
  · have h1 : ∑ i, C (algebraMap F F' (b.repr a i)) *
        (C (b i) * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') (G i)) ∈ V' :=
      Ideal.sum_mem _ fun i _ => V'.mul_mem_left _ (hV i)
    have h2 : (C a : MRing ι F') = ∑ i, C (algebraMap F F' (b.repr a i)) * C (b i) := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [map_sum, Algebra.smul_def, map_mul]
    convert h1 using 1
    rw [h2]
    simp only [map_sum, map_mul, map_C, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]

theorem lift_form [∀ k, Fintype (ι k)] {n : ℕ} (h : ∀ c a, Good (F := F) V' n c a) {m : K → ℕ}
    (hm : ∀ k, n * Fintype.card (ι k) < m k) {q : MRing ι F'} (hq : IsMultiHomog q m) :
    ∃ p : MRing ι F, IsMultiHomog p m ∧ q - MvPolynomial.map (algebraMap F F') p ∈ V' := by
  rw [q.as_sum]
  refine Finset.sum_induction _
    (fun q => ∃ p : MRing ι F, IsMultiHomog p m ∧ q - MvPolynomial.map (algebraMap F F') p ∈ V') ?_ ?_ ?_
  · rintro q₁ q₂ ⟨p₁, h₁, k₁⟩ ⟨p₂, h₂, k₂⟩
    refine ⟨p₁ + p₂, IsWeightedHomogeneous.add h₁ h₂, ?_⟩
    convert V'.add_mem k₁ k₂ using 1
    rw [map_add]
    ring
  · exact ⟨0, isWeightedHomogeneous_zero _ _ _, by simp⟩
  · intro d hd
    have hw : Finsupp.weight (blockWeight ι) d = m := hq (mem_support_iff.1 hd)
    obtain ⟨c, hc⟩ := exists_chart (n := n) (d := d) (by rw [hw]; exact hm)
    obtain ⟨d', hd'⟩ := exists_add_of_le (ex_le hc)
    obtain ⟨G, hG, hV⟩ := h c (coeff d q)
    refine ⟨G * monomial d' 1, ?_, ?_⟩
    · have h1 := IsWeightedHomogeneous.mul hG
        (isWeightedHomogeneous_monomial (R := F) (blockWeight ι) d' 1 rfl)
      have h2 : (fun _ => n) + Finsupp.weight (blockWeight ι) d' = m := by
        rw [← hw, hd', map_add, weight_ex]
      rw [h2] at h1
      exact h1
    · have h1 := V'.mul_mem_right (monomial d' 1) hV
      have h2 : (monomial d (coeff d q) : MRing ι F') =
          C (coeff d q) * (∏ k, X ⟨k, c k⟩) ^ n * monomial d' 1 := by
        rw [chart_pow, mul_assoc, monomial_mul, ← hd', C_mul_monomial]
        simp
      rw [h2, map_mul, map_monomial, (algebraMap F F').map_one, ← sub_mul]
      exact h1

omit [Fintype K] in
theorem finrank_piece {m : K → ℕ}
    (h : ∀ q : MRing ι F', IsMultiHomog q m →
      ∃ p : MRing ι F, IsMultiHomog p m ∧ q - MvPolynomial.map (algebraMap F F') p ∈ V') :
    Module.finrank F (gradedPiece (V'.comap (MvPolynomial.map (algebraMap F F'))) m) =
      Module.finrank F F' * Module.finrank F' (gradedPiece V' m) := by
  set V := V'.comap (MvPolynomial.map (algebraMap F F')) with hVdef
  have hφ : ∀ p : MRing ι F, mapAlgHom (Algebra.ofId F F') p = MvPolynomial.map (algebraMap F F') p :=
    fun p => rfl
  let ψ : (MRing ι F ⧸ V) →ₐ[F] (MRing ι F' ⧸ V') :=
    Ideal.Quotient.liftₐ V ((Ideal.Quotient.mkₐ F V').comp (mapAlgHom (Algebra.ofId F F')))
      (fun p hp => Ideal.Quotient.eq_zero_iff_mem.2 hp)
  have hψ : ∀ p, ψ (Ideal.Quotient.mk V p) =
      Ideal.Quotient.mk V' (MvPolynomial.map (algebraMap F F') p) := fun p => rfl
  have hinj : Function.Injective ψ.toLinearMap := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hψ, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  have hmap : (gradedPiece V m).map ψ.toLinearMap = (gradedPiece V' m).restrictScalars F := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨MvPolynomial.map (algebraMap F F') p, ?_, (hψ p).symm⟩
      intro d hd
      refine hp fun h0 => hd ?_
      rw [coeff_map, h0, map_zero]
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨p, hp, hV⟩ := h q hq
      refine ⟨Ideal.Quotient.mk V p, ⟨p, hp, rfl⟩, ?_⟩
      exact (hψ p).trans (Ideal.Quotient.eq.2 hV).symm
  rw [(Submodule.equivMapOfInjective _ hinj (gradedPiece V m)).finrank_eq, hmap,
    Module.finrank_mul_finrank]
  exact ((Submodule.restrictScalarsEquiv F F' _ (gradedPiece V' m)).restrictScalars F).finrank_eq

end Fields

end BaseChangeColon.PlField

theorem BaseChangeColon.intNumL_comap_base_extension : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F'] (V' : Ideal (MRing ι F')), IsMultiHomogIdeal V' → (∀ (c : ∀ k, ι k) (a : F'), ∃ (n : ℕ) (G : MRing ι F), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') G ∈ V') → ∀ l : List (K → ℤ), intNumL F (V'.comap (MvPolynomial.map (algebraMap F F'))) l = (Module.finrank F F' : ℤ) * intNumL F' V' l := by
  intro K _ _ ι _ F F' _ _ _ _ V' _ h l
  obtain ⟨n, hn⟩ := BaseChangeColon.PlField.exists_uniform (F := F) (V' := V') h
  have hc : (Module.finrank F F' : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := F')).ne'
  refine BaseChangeColon.PlField.eventualValue_mul hc (BaseChangeColon.PlField.foldr_eventually _ _ ?_)
  filter_upwards [Filter.eventually_ge_atTop fun k => ((n * Fintype.card (ι k) + 1 : ℕ) : ℤ)] with m hm
  have h0 : ∀ k, 0 ≤ m k := fun k => le_trans (Int.natCast_nonneg _) (hm k)
  have h1 : ∀ k, n * Fintype.card (ι k) < (m k).toNat := fun k => by
    have h2 : ((n * Fintype.card (ι k) + 1 : ℕ) : ℤ) ≤ m k := hm k
    generalize n * Fintype.card (ι k) = t at h2 ⊢
    omega
  rw [hilbFn, hilbFn, if_pos h0, if_pos h0,
    BaseChangeColon.PlField.finrank_piece fun q hq => BaseChangeColon.PlField.lift_form hn h1 hq]
  push_cast
  rfl
