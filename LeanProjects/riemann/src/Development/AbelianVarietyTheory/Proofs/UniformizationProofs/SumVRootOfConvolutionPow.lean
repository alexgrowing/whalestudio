import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumVOfConvolution
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem le_v_sum_sub_sum {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F}
    (q : ℚ) {S T : Finset Ix} (hST : S ⊆ T) (hS : ∀ i, i ∉ S → (q : WithTop ℚ) ≤ v (x i)) :
    (q : WithTop ℚ) ≤ v (∑ i ∈ T, x i - ∑ i ∈ S, x i) := by
  classical
  rw [← Finset.sum_sdiff hST, add_sub_cancel_right]
  exact v.map_le_sum fun i hi => hS i (Finset.mem_sdiff.1 hi).2

theorem partial_sum_convolution {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type} [AddCommGroup X]
    {a b c : X → F} (ha : NullV v a) (hb : NullV v b)
    (hc : ∀ α, SumV v (fun χ => a χ * b (α - χ)) (c α)) (q : ℚ) :
    ∀ᶠ T : Finset X in Filter.atTop,
      (q : WithTop ℚ) ≤ v (∑ i ∈ T, c i - (∑ i ∈ T, a i) * ∑ i ∈ T, b i) := by
  classical
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  obtain ⟨mb, hmb⟩ := nullV_bdd v hb
  set Sa := (ha (q - mb)).toFinset with hSa
  set Sb := (hb (q - ma)).toFinset with hSb
  have hSa' : ∀ χ, χ ∉ Sa → ((q - mb : ℚ) : WithTop ℚ) ≤ v (a χ) := fun χ hχ =>
    not_lt.1 fun h => hχ ((Set.Finite.mem_toFinset _).2 h)
  have hSb' : ∀ β, β ∉ Sb → ((q - ma : ℚ) : WithTop ℚ) ≤ v (b β) := fun β hβ =>
    not_lt.1 fun h => hβ ((Set.Finite.mem_toFinset _).2 h)
  filter_upwards [Filter.eventually_ge_atTop Sa, Filter.eventually_ge_atTop Sb,
    Filter.eventually_ge_atTop (Finset.image₂ (· + ·) Sa Sb)] with T hTa hTb hTU
  have h1 : ∀ α, (q : WithTop ℚ) ≤ v (c α - ∑ χ ∈ Sa, a χ * b (α - χ)) := fun α =>
    sumV_tail v (hc α) q Sa fun χ hχ => le_v_mul v (hSa' χ hχ) (hmb _) (by ring)
  have h4 : (q : WithTop ℚ) ≤ v (∑ α ∈ T, (c α - ∑ χ ∈ Sa, a χ * b (α - χ))) :=
    v.map_le_sum fun α _ => h1 α
  have h5 : ∀ χ ∈ Sa, ((q - ma : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ T, b (α - χ) - ∑ α ∈ T, b α) := by
    intro χ hχ
    have e : ∑ α ∈ T, b (α - χ) = ∑ β ∈ T.image (· - χ), b β :=
      (Finset.sum_image (f := b) (g := (· - χ)) fun x _ y _ h => sub_left_injective h).symm
    have hsub : Sb ⊆ T.image (· - χ) := fun β h =>
      Finset.mem_image.2 ⟨χ + β, hTU (Finset.mem_image₂.2 ⟨χ, hχ, β, h, rfl⟩), by simp⟩
    have := v.map_le_sub (le_v_sum_sub_sum v _ hsub hSb') (le_v_sum_sub_sum v _ hTb hSb')
    rwa [sub_sub_sub_cancel_right, ← e] at this
  have h6 : (q : WithTop ℚ) ≤ v (∑ χ ∈ Sa, a χ * (∑ α ∈ T, b (α - χ) - ∑ α ∈ T, b α)) :=
    v.map_le_sum fun χ hχ => le_v_mul v (hma χ) (h5 χ hχ) (by ring)
  have h7 : (q : WithTop ℚ) ≤ v ((∑ i ∈ T, a i - ∑ i ∈ Sa, a i) * ∑ i ∈ T, b i) :=
    le_v_mul v (le_v_sum_sub_sum v _ hTa hSa') (v.map_le_sum fun i _ => hmb i) (by ring)
  have h8 := v.map_le_sub (v.map_le_add h4 h6) h7
  have e : ∑ i ∈ T, c i - (∑ i ∈ T, a i) * ∑ i ∈ T, b i =
      ∑ α ∈ T, (c α - ∑ χ ∈ Sa, a χ * b (α - χ)) +
        ∑ χ ∈ Sa, a χ * (∑ α ∈ T, b (α - χ) - ∑ α ∈ T, b α) -
        (∑ i ∈ T, a i - ∑ i ∈ Sa, a i) * ∑ i ∈ T, b i := by
    have e2 : ∑ α ∈ T, ∑ χ ∈ Sa, a χ * b (α - χ) = ∑ χ ∈ Sa, a χ * ∑ α ∈ T, b (α - χ) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    simp only [Finset.sum_sub_distrib, mul_sub, ← Finset.sum_mul]
    rw [e2]
    ring
  rw [e]
  exact h8

theorem partial_sum_convolution_pow {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type}
    [AddCommGroup X] {a : X → F} {c : ℕ → X → F} (h0 : c 0 = a) (hn : ∀ j, NullV v (c j))
    (hc : ∀ j α, SumV v (fun χ => c j χ * a (α - χ)) (c (j + 1) α)) (j : ℕ) (q : ℚ) :
    ∀ᶠ T : Finset X in Filter.atTop,
      (q : WithTop ℚ) ≤ v (∑ i ∈ T, c j i - (∑ i ∈ T, a i) ^ (j + 1)) := by
  have ha : NullV v a := h0 ▸ hn 0
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  induction j generalizing q with
  | zero => exact Filter.Eventually.of_forall fun T => by simp [h0]
  | succ j ih =>
    filter_upwards [ih (q - ma), partial_sum_convolution v (hn j) ha (hc j) q] with T h1 h2
    have h3 : (q : WithTop ℚ) ≤ v ((∑ i ∈ T, c j i - (∑ i ∈ T, a i) ^ (j + 1)) * ∑ i ∈ T, a i) :=
      le_v_mul v h1 (v.map_le_sum fun i _ => hma i) (by ring)
    have h4 := v.map_le_add h2 h3
    convert h4 using 2
    ring

theorem v_multiset_prod_le {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (Q : ℚ) (s : Multiset F)
    (h : ∀ x ∈ s, v x ≤ (Q : WithTop ℚ)) : v s.prod ≤ (((s.card : ℚ) * Q : ℚ) : WithTop ℚ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.prod_cons, v.map_mul, Multiset.card_cons]
    have e : (((s.card + 1 : ℕ) : ℚ) * Q : ℚ) = Q + (s.card : ℚ) * Q := by push_cast; ring
    rw [e, WithTop.coe_add]
    exact add_le_add (h x (Multiset.mem_cons_self _ _)) (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

theorem sumV_root_of_convolution_pow : ∀ (F : Type) [Field F] [IsAlgClosed F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] (a : X → F) (c : ℕ → X → F), c 0 = a → (∀ j, NullV v (c j)) → (∀ j α, SumV v (fun χ => c j χ * a (α - χ)) (c (j + 1) α)) → ∀ (m : ℕ) (β : F), SumV v (c m) β → ∃ r : F, SumV v a r ∧ r ^ (m + 1) = β := by
  classical
  intro F _ _ v X _ a c h0 hn hc m β hβ
  have ha : NullV v a := h0 ▸ hn 0
  by_contra hcon
  set p : Polynomial F := Polynomial.X ^ (m + 1) - Polynomial.C β with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C β (Nat.succ_ne_zero m)
  have hroot : ∀ r ∈ p.roots, r ^ (m + 1) = β := by
    intro r hr
    have := (Polynomial.mem_roots hmon.ne_zero).1 hr
    simpa [hp, sub_eq_zero] using this
  have hfar : ∀ r : F, ∃ q : ℚ, r ∈ p.roots →
      ∀ᶠ T : Finset X in Filter.atTop, v (∑ i ∈ T, a i - r) ≤ (q : WithTop ℚ) := by
    intro r
    by_cases hr : r ∈ p.roots
    · have h1 : ¬ SumV v a r := fun h => hcon ⟨r, h, hroot r hr⟩
      obtain ⟨q, hq⟩ := not_forall.1 h1
      refine ⟨q, fun _ => ?_⟩
      filter_upwards [Filter.eventually_ge_atTop (ha q).toFinset] with T hT
      by_contra hlt
      refine hq ⟨T, fun T' hT' => ?_⟩
      have h2 := le_v_sum_sub_sum v q hT' (x := a) fun i hi =>
        not_lt.1 fun h => hi (hT ((Set.Finite.mem_toFinset _).2 h))
      have h3 := v.map_le_add h2 (not_le.1 hlt).le
      rw [sub_add_sub_cancel, v.map_sub_swap] at h3
      exact h3
    · exact ⟨0, fun h => absurd h hr⟩
  choose qf hqf using hfar
  obtain ⟨Q, hQ⟩ := (p.roots.toFinset.image qf).finite_toSet.bddAbove
  have hQ' : ∀ r ∈ p.roots, qf r ≤ Q := fun r hr =>
    hQ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.2 hr)))
  have e1 : ∀ᶠ T : Finset X in Filter.atTop, ∀ r ∈ p.roots.toFinset,
      v (∑ i ∈ T, a i - r) ≤ (qf r : WithTop ℚ) :=
    (Filter.eventually_all_finset _).2 fun r hr => hqf r (Multiset.mem_toFinset.1 hr)
  set q : ℚ := (p.roots.card : ℚ) * Q + 1 with hq
  have e2 := partial_sum_convolution_pow v h0 hn hc m q
  have e3 : ∀ᶠ T : Finset X in Filter.atTop, (q : WithTop ℚ) ≤ v (β - ∑ i ∈ T, c m i) :=
    Filter.eventually_atTop.2 (hβ q)
  obtain ⟨T, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  have h4 := v.map_le_add h3 h2
  rw [sub_add_sub_cancel, v.map_sub_swap] at h4
  have h5 : (∑ i ∈ T, a i) ^ (m + 1) - β = (p.roots.map fun r => ∑ i ∈ T, a i - r).prod := by
    have := (IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmon (∑ i ∈ T, a i)
    simpa [hp] using this
  have h6 := v_multiset_prod_le v Q (p.roots.map fun r => ∑ i ∈ T, a i - r) (by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    exact (h1 r (Multiset.mem_toFinset.2 hr)).trans (WithTop.coe_le_coe.2 (hQ' r hr)))
  rw [← h5, Multiset.card_map] at h6
  have h7 := WithTop.coe_le_coe.1 (h4.trans h6)
  linarith

end GlobalTheory.UT
