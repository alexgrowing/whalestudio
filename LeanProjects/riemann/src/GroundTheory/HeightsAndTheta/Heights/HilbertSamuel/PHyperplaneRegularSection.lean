import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneRegularSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HyperplaneRegularSection

theorem exists_notMem_of_finite {V : Type*} [AddCommGroup V] [Module ℚ V] (S : Set (Submodule ℚ V))
    (hS : S.Finite) (htop : ∀ W ∈ S, W ≠ ⊤) : ∃ v : V, ∀ W ∈ S, v ∉ W := by
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := ℚ) (E := V) (s := hS.toFinset)
    (by rw [Set.Finite.mem_toFinset]; exact fun h => htop ⊤ h rfl)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨v, fun W hW hvW => hv ?_⟩
  exact Set.mem_biUnion ((Set.Finite.mem_toFinset hS).mpr hW) hvW

theorem mem_span_of_mul_mem {A : Type*} [CommRing A] [IsNoetherianRing A] (f w u : A)
    (hw : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {f}), w ∉ p) (h : w * u ∈ Ideal.span {f}) :
    u ∈ Ideal.span {f} := by
  by_contra hu
  have hx : (Ideal.Quotient.mk (Ideal.span {f}) u) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmem : w ∈ {r : A | ∃ x : A ⧸ Ideal.span {f}, x ≠ 0 ∧ r • x = 0} :=
    ⟨_, hx, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]; exact h⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hmem
  obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hmem
  exact hw p hp hwp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isNoetherianRing_chartRingQ (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) :
    IsNoetherianRing (chartRingQ y c') := by
  classical
  refine isNoetherianRing_of_fg ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

def gen (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (i : ι k) : chartRingQ y c' :=
  ⟨y ⟨k, i⟩ / y ⟨k, c' k⟩, Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩⟩

def eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) : chartRingQ y c' :=
  ∏ k, gen y c' k (c k)

def avoidSub (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (p : Ideal (chartRingQ y c')) :
    Submodule ℚ (ι k → ℚ) :=
  (p.restrictScalars ℚ).comap (Fintype.linearCombination ℚ (gen y c' k))

def twist (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))

omit [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem twist_add (y : (Σ k, ι k) → Ω) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) :
    twist y c' (a + a') = twist y c' a * twist y c' a' := by
  simp only [twist, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc' k)]
  congr 1
  simp only [Pi.add_apply]
  ring

omit [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem twist_zero (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) : twist y c' 0 = 1 := by
  simp [twist]

omit [∀ k, Fintype (ι k)] in

theorem coe_eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) :
    (eqn y c c' : Ω) = (∏ k, y ⟨k, c k⟩) * twist y c' 1 := by
  simp only [eqn, gen, twist, Pi.one_apply]
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end HyperplaneRegularSection

set_option synthInstance.maxHeartbeats 400000 in
open HyperplaneRegularSection in

theorem HyperplaneRegularSection.proof : HyperplaneRegularSection.Statement := by
  intro K _ ι _ Ω _ _ y c e hc
  classical
  have hnoeth : ∀ c' : ∀ k, ι k, IsNoetherianRing (chartRingQ y c') := isNoetherianRing_chartRingQ y

  have hlam : ∀ k, ∃ v : ι k → ℚ, ∑ i, v i • y ⟨k, i⟩ ≠ 0 ∧
      ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
        ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}),
          Fintype.linearCombination ℚ (gen y c' k) v ∉ p := by
    intro k
    let S : Set (Submodule ℚ (ι k → ℚ)) :=
      {LinearMap.ker (Fintype.linearCombination ℚ fun i => y ⟨k, i⟩)} ∪
        ⋃ c' : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0},
          avoidSub y c'.1 k '' associatedPrimes (chartRingQ y c'.1)
            (chartRingQ y c'.1 ⧸ Ideal.span {eqn y c c'.1})
    have hS : S.Finite := (Set.finite_singleton _).union
      (Set.finite_iUnion fun c' => (associatedPrimes.finite _ _).image _)
    have htop : ∀ W ∈ S, W ≠ ⊤ := by
      intro W hW hWtop
      rcases hW with hW | hW
      · rw [Set.mem_singleton_iff] at hW
        have h1 : Pi.single (c k) (1 : ℚ) ∈ W := hWtop ▸ Submodule.mem_top
        rw [hW, LinearMap.mem_ker, Fintype.linearCombination_apply_single, one_smul] at h1
        exact hc k h1
      · obtain ⟨c', p, hp, rfl⟩ := Set.mem_iUnion.mp hW
        have h1 : Pi.single (c'.1 k) (1 : ℚ) ∈ avoidSub y c'.1 k p := hWtop ▸ Submodule.mem_top
        rw [avoidSub, Submodule.mem_comap, Submodule.restrictScalars_mem,
          Fintype.linearCombination_apply_single, one_smul,
          show gen y c'.1 k (c'.1 k) = 1 from Subtype.ext (div_self (c'.2 k))] at h1
        exact (IsAssociatedPrime.isPrime hp).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨v, hv⟩ := exists_notMem_of_finite S hS htop
    refine ⟨v, fun h0 => hv _ (Or.inl rfl) ?_, fun c' hc' p hp hvp =>
      hv _ (Or.inr (Set.mem_iUnion.mpr ⟨⟨c', hc'⟩, p, hp, rfl⟩)) hvp⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact h0
  choose v hv0 hvp using hlam
  set m := ∏ k, y ⟨k, c k⟩ with hm_def
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  set l : K → Ω := fun k => ∑ i, v k i • y ⟨k, i⟩ with hl
  set σ : Ω := ∏ k, l k ^ e k with hσ

  have hφ : ∀ (c' : ∀ k, ι k) (k : K),
      ((Fintype.linearCombination ℚ (gen y c' k) (v k) : chartRingQ y c') : Ω) = l k / y ⟨k, c' k⟩ := by
    intro c' k
    simp [Fintype.linearCombination_apply, gen, hl, Finset.sum_div, smul_div_assoc]
  let w : ∀ c' : ∀ k, ι k, chartRingQ y c' := fun c' =>
    ∏ k, Fintype.linearCombination ℚ (gen y c' k) (v k) ^ e k
  have hw : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (w c' : Ω) = σ * twist y c' (fun k => (e k : ℤ)) := by
    intro c' hc'
    simp only [w, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, hφ, twist, hσ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, zpow_neg, Nat.cast_one, one_mul, zpow_natCast, div_eq_mul_inv]
  have hwp : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}), w c' ∉ p := by
    intro c' hc' p hp hwp
    have := IsAssociatedPrime.isPrime hp
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hwp
    exact hvp k c' hc' p hp (this.mem_of_pow_mem _ hk)
  refine ⟨σ, Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hv0 k), ?_, ?_⟩
  · intro c' hc'
    show σ * twist y c' (fun k => (e k : ℤ)) ∈ chartRingQ y c'
    rw [← hw c' hc']
    exact (w c').2
  · intro b s hs h c' hc'
    have hnc := hnoeth c'
    have hT : twist y c' 1 * twist y c' (-1) = 1 := by
      rw [← twist_add y hc', add_neg_cancel, twist_zero]
    have hM : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    let u : chartRingQ y c' := ⟨s * twist y c' b, hs c' hc'⟩
    let u' : chartRingQ y c' :=
      ⟨σ * s / m * twist y c' (b + (fun k => (e k : ℤ)) - 1), h c' hc'⟩
    have key : w c' * u = eqn y c c' * u' := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, u, u']
      rw [hw c' hc', coe_eqn, ← hm_def, sub_eq_add_neg, twist_add y hc', twist_add y hc']
      linear_combination (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ)))) * hM +
        (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ))) * (m * m⁻¹)) * hT
    have hu : u ∈ Ideal.span {eqn y c c'} :=
      mem_span_of_mul_mem _ _ _ (hwp c' hc') (by
        rw [key]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
    have ha' : (a : Ω) * (m * twist y c' 1) = s * twist y c' b := by
      rw [← coe_eqn]
      exact congrArg Subtype.val ha
    show s / m * twist y c' (b - 1) ∈ chartRingQ y c'
    have heq : s / m * twist y c' (b - 1) = a := by
      rw [sub_eq_add_neg, twist_add y hc', div_eq_mul_inv]
      linear_combination (-(m⁻¹ * twist y c' (-1))) * ha' + ((a : Ω) * (twist y c' 1 * twist y c' (-1))) * hM +
        (a : Ω) * hT
    rw [heq]
    exact a.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
