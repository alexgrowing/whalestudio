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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem sumV_tail {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (q : ℚ) (S : Finset Ix) (hS : ∀ i, i ∉ S → (q : WithTop ℚ) ≤ v (x i)) :
    (q : WithTop ℚ) ≤ v (s - ∑ i ∈ S, x i) := by
  classical
  obtain ⟨S', hS'⟩ := h q
  have h1 := hS' (S ∪ S') Finset.subset_union_right
  have h2 : (q : WithTop ℚ) ≤ v (∑ i ∈ (S ∪ S') \ S, x i) :=
    v.map_le_sum fun i hi => hS i (Finset.mem_sdiff.1 hi).2
  have h3 := Finset.sum_sdiff (f := x) (Finset.subset_union_left (s₁ := S) (s₂ := S'))
  have h4 : s - ∑ i ∈ S, x i = (s - ∑ i ∈ S ∪ S', x i) + ∑ i ∈ (S ∪ S') \ S, x i := by
    rw [← h3]; ring
  rw [h4]
  exact v.map_le_add h1 h2

theorem nullV_bdd {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {x : Ix → F}
    (h : NullV v x) : ∃ m : ℚ, ∀ i, (m : WithTop ℚ) ≤ v (x i) := by
  have hf := (h 0).image (fun i => (v (x i)).untopD 0)
  obtain ⟨m, hm⟩ := hf.bddBelow
  refine ⟨min m 0, fun i => ?_⟩
  by_cases hi : v (x i) < ((0 : ℚ) : WithTop ℚ)
  · have h1 := hm ⟨i, hi, rfl⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hi)
    simp only [← hr, WithTop.untopD_coe] at h1
    rw [← hr]
    exact WithTop.coe_le_coe.2 ((min_le_left _ _).trans h1)
  · exact (WithTop.coe_le_coe.2 (min_le_right _ _)).trans (not_lt.1 hi)

theorem le_v_mul {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {x y : F} {p r q : ℚ}
    (hx : (p : WithTop ℚ) ≤ v x) (hy : (r : WithTop ℚ) ≤ v y) (h : q = p + r) : (q : WithTop ℚ) ≤ v (x * y) := by
  rw [v.map_mul, h, WithTop.coe_add]
  exact add_le_add hx hy

theorem sumV_of_convolution : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] (a b c : X → F), NullV v a → NullV v b → (∀ α, SumV v (fun χ => a χ * b (α - χ)) (c α)) → ∀ sb sc : F, SumV v b sb → SumV v c sc → sb ≠ 0 → SumV v a (sc / sb) := by
  classical
  intro F _ v X _ a b c ha hb hc sb sc hsb hsc h0 q
  obtain ⟨ma, hma⟩ := nullV_bdd v ha
  obtain ⟨mb, hmb⟩ := nullV_bdd v hb
  have hinv : v sb⁻¹ ≠ ⊤ := v.ne_top_iff.2 (inv_ne_zero h0)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hinv
  set q' : ℚ := q - r with hq'
  refine ⟨(ha (q' - mb)).toFinset, fun T hT => ?_⟩
  set Sb := (hb (q' - ma)).toFinset with hSb
  have hTa : ∀ χ, χ ∉ T → ((q' - mb : ℚ) : WithTop ℚ) ≤ v (a χ) := fun χ hχ =>
    not_lt.1 fun h => hχ (hT ((Set.Finite.mem_toFinset _).2 h))
  have hSb' : ∀ β, β ∉ Sb → ((q' - ma : ℚ) : WithTop ℚ) ≤ v (b β) := fun β hβ =>
    not_lt.1 fun h => hβ ((Set.Finite.mem_toFinset _).2 h)
  set U : Finset X := Finset.image₂ (· + ·) T Sb with hU
  have h1 : ∀ α, (q' : WithTop ℚ) ≤ v (c α - ∑ χ ∈ T, a χ * b (α - χ)) := fun α =>
    sumV_tail v (hc α) q' T fun χ hχ => le_v_mul v (hTa χ hχ) (hmb _) (by ring)
  have h2 : ∀ α, α ∉ U → (q' : WithTop ℚ) ≤ v (c α) := by
    intro α hα
    have : (q' : WithTop ℚ) ≤ v (∑ χ ∈ T, a χ * b (α - χ)) := by
      refine v.map_le_sum fun χ hχ => le_v_mul v (hma _) (hSb' _ fun h => hα ?_) (by ring)
      exact Finset.mem_image₂.2 ⟨χ, hχ, α - χ, h, by simp⟩
    have h3 := v.map_le_add (h1 α) this
    rwa [sub_add_cancel] at h3
  have h3 := sumV_tail v hsc q' U h2
  have h4 : (q' : WithTop ℚ) ≤ v (∑ α ∈ U, (c α - ∑ χ ∈ T, a χ * b (α - χ))) :=
    v.map_le_sum fun α _ => h1 α
  have h5 : ∀ χ ∈ T, ((q' - ma : ℚ) : WithTop ℚ) ≤ v (sb - ∑ α ∈ U, b (α - χ)) := by
    intro χ hχ
    have e : ∑ α ∈ U, b (α - χ) = ∑ β ∈ U.image (· - χ), b β :=
      (Finset.sum_image (f := b) (g := (· - χ)) fun x _ y _ h => sub_left_injective h).symm
    rw [e]
    refine sumV_tail v hsb _ _ fun β hβ => hSb' β fun h => hβ ?_
    exact Finset.mem_image.2 ⟨χ + β, Finset.mem_image₂.2 ⟨χ, hχ, β, h, rfl⟩, by simp⟩
  have h6 : (q' : WithTop ℚ) ≤ v (∑ χ ∈ T, a χ * (sb - ∑ α ∈ U, b (α - χ))) :=
    v.map_le_sum fun χ hχ => le_v_mul v (hma χ) (h5 χ hχ) (by ring)
  have h7 := v.map_le_sub (v.map_le_add h3 h4) h6
  have e : sc / sb - ∑ i ∈ T, a i =
      (sc - ∑ i ∈ U, c i + ∑ α ∈ U, (c α - ∑ χ ∈ T, a χ * b (α - χ)) -
        ∑ χ ∈ T, a χ * (sb - ∑ α ∈ U, b (α - χ))) * sb⁻¹ := by
    simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm (s := U) (t := T)]
    field_simp
    ring
  rw [e]
  exact le_v_mul v h7 hr.le (by rw [hq']; ring)

end GlobalTheory.UT
