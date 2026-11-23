import Mathlib
import GroundTheory.ProfiniteCohomology.CyclicCupBrauer
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

namespace OrderTwo

section Group

variable {G : Type} [Group G] {c : G}

theorem mul_self_eq_one (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1) : c * c = 1 := by
  rcases hG (c * c) with h | h
  · exact h
  · exact absurd (mul_eq_left.1 h) hc

theorem inv_eq_self (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1) : c⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one hG hc)

end Group

section Differentials

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

theorem d_zero_apply (f : (Fin 0 → G) → A) (g : G) :
    (inhomogeneousCochains.d A 0).hom f ![g] = A.ρ g (f Fin.elim0) - f Fin.elim0 := by
  have h : ∀ x : Fin 0 → G, f x = f Fin.elim0 := fun x => by rw [Subsingleton.elim x Fin.elim0]
  simp [inhomogeneousCochains.d_hom_apply, h]
  abel

theorem d_one_apply (w : (Fin 1 → G) → A) (g h : G) :
    (inhomogeneousCochains.d A 1).hom w ![g, h] = A.ρ g (w ![h]) - w ![g * h] + w ![g] := by
  refine (inhomogeneousCochains_d_one_apply A _ ![g, h]).trans ?_
  have e1 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 1) = ![h] := by
    funext i; fin_cases i; rfl
  have e2 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0 * (![g, h] : Fin 2 → G) 1) = ![g * h] := by
    funext i; fin_cases i; rfl
  have e3 : (fun _ : Fin 1 => (![g, h] : Fin 2 → G) 0) = ![g] := by
    funext i; fin_cases i; rfl
  rw [e1, e2, e3]
  rfl

theorem d_two_apply (f : (Fin 2 → G) → A) (g h j : G) :
    (inhomogeneousCochains.d A 2).hom f ![g, h, j] =
      A.ρ g (f ![h, j]) - f ![g * h, j] + f ![g, h * j] - f ![g, h] := by
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_three]
  have h0 : Fin.contractNth (0 : Fin 3) (· * ·) ![g, h, j] = ![g * h, j] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp)]; rfl
  have h1 : Fin.contractNth (1 : Fin 3) (· * ·) ![g, h, j] = ![g, h * j] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp)]; rfl
  have h2 : Fin.contractNth (2 : Fin 3) (· * ·) ![g, h, j] = ![g, h] := by
    funext i
    fin_cases i
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
    · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  have h3 : (fun i : Fin 2 => (![g, h, j] : Fin 3 → G) i.succ) = ![h, j] := by
    funext i
    fin_cases i <;> rfl
  rw [h0, h1, h2, h3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_one, neg_smul, one_smul,
    Nat.reduceAdd, even_two, Even.neg_pow, one_pow]
  have : ((-1 : k) ^ 3) = -1 := by norm_num
  rw [this, neg_smul, one_smul]
  show A.ρ g (f ![h, j]) + (-f ![g * h, j] + f ![g, h * j] + -f ![g, h]) = _
  abel

end Differentials

section Classes

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem cochainOf_d_zero (w : (cochainsComplex A).X 0) (g : G) :
    cochainOf A (((cochainsComplex A).d 0 1).hom w) ![g] =
      A.ρ g (cochainOf A w Fin.elim0) - cochainOf A w Fin.elim0 :=
  (congrFun (cochainOf_d (A := A) w) ![g]).trans (d_zero_apply A _ g)

theorem cochainOf_d_one (w : (cochainsComplex A).X 1) (g h : G) :
    cochainOf A (((cochainsComplex A).d 1 2).hom w) ![g, h] =
      A.ρ g (cochainOf A w ![h]) - cochainOf A w ![g * h] + cochainOf A w ![g] :=
  (congrFun (cochainOf_d (A := A) w) ![g, h]).trans (d_one_apply A _ g h)

theorem cochainOf_d_two (w : (cochainsComplex A).X 2) (g h j : G) :
    cochainOf A (((cochainsComplex A).d 2 3).hom w) ![g, h, j] =
      A.ρ g (cochainOf A w ![h, j]) - cochainOf A w ![g * h, j] + cochainOf A w ![g, h * j] -
        cochainOf A w ![g, h] :=
  (congrFun (cochainOf_d (A := A) w) ![g, h, j]).trans (d_two_apply A _ g h j)

theorem cochainOf_sub {i : ℕ} (a b : (cochainsComplex A).X i) :
    cochainOf A (a - b) = cochainOf A a - cochainOf A b :=
  rfl

theorem cocycle_one (z : cocycles A 1) (g h : G) :
    A.ρ g (cochainOf A (cocycleι A 1 z) ![h]) - cochainOf A (cocycleι A 1 z) ![g * h] +
      cochainOf A (cocycleι A 1 z) ![g] = 0 := by
  rw [← d_one_apply]
  exact congrFun (d_cocycleι z) ![g, h]

theorem cocycle_two (z : cocycles A 2) (g h j : G) :
    A.ρ g (cochainOf A (cocycleι A 2 z) ![h, j]) - cochainOf A (cocycleι A 2 z) ![g * h, j] +
      cochainOf A (cocycleι A 2 z) ![g, h * j] - cochainOf A (cocycleι A 2 z) ![g, h] = 0 := by
  rw [← d_two_apply]
  exact congrFun (d_cocycleι z) ![g, h, j]

variable [DiscreteTopology G]

theorem cohomologyπ_one_eq_zero_iff (z : cocycles A 1) :
    cohomologyπ A 1 z = 0 ↔
      ∃ m : A, ∀ g : G, cochainOf A (cocycleι A 1 z) ![g] = A.ρ g m - m := by
  change ((cochainsComplex A).homologyπ 1).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cochainOf A w Fin.elim0, fun g => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g]) hw
    rw [cochainOf_d_zero] at e
    exact e.symm
  · rintro ⟨m, hm⟩
    refine ⟨mkCochain A (fun _ => m) (IsLocallyConstant.of_discrete _), ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0] := by funext i; fin_cases i; rfl
    rw [hv, cochainOf_d_zero]
    exact (hm (v 0)).symm

theorem cohomologyπ_two_eq_zero_iff (z : cocycles A 2) :
    cohomologyπ A 2 z = 0 ↔ ∃ f : G → A, ∀ g h : G,
      cochainOf A (cocycleι A 2 z) ![g, h] = A.ρ g (f h) - f (g * h) + f g := by
  change ((cochainsComplex A).homologyπ 2).hom z = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun g => cochainOf A w ![g], fun g h => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g, h]) hw
    rw [cochainOf_d_one] at e
    exact e.symm
  · rintro ⟨f, hfz⟩
    refine ⟨mkCochain A (fun v : Fin 1 → G => f (v 0))
      ((IsLocallyConstant.of_discrete f).comp_continuous (continuous_apply 0)), ?_⟩
    apply cochainOf_injective
    funext v
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, cochainOf_d_one]
    exact (hfz (v 0) (v 1)).symm

end Classes

section OrderTwo

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

open Classical in

def cochainOne (α : A) : (Fin 1 → G) → A := fun v => if v 0 = 1 then 0 else α

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainOne_one (α : A) : cochainOne A α ![1] = 0 := by
  simp [cochainOne]

include hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainOne_c (α : A) : cochainOne A α ![c] = α := by
  simp [cochainOne, hc]

include hG hc in

theorem d_cochainOne (α : A) (hα : α + A.ρ c α = 0) :
    (cochainsComplex A).d 1 2 (mkCochain A (cochainOne A α) (IsLocallyConstant.of_discrete _)) =
      0 := by
  apply cochainOf_injective
  funext v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, cochainOf_d_one, cochainOf_mkCochain, cochainOf_zero, Pi.zero_apply]
  have hcc := mul_self_eq_one hG hc
  rcases hG (v 0) with h0 | h0 <;> rcases hG (v 1) with h1 | h1 <;>
    simp [h0, h1, hcc, cochainOne_one, cochainOne_c A hc]
  rw [add_comm]
  exact hα

def cocycleOne (α : A) (hα : α + A.ρ c α = 0) : cocycles A 1 :=
  (cochainsComplex A).cyclesMk (mkCochain A (cochainOne A α) (IsLocallyConstant.of_discrete _)) 2
    (by simp) (d_cochainOne A hG hc α hα)

theorem cochainOf_cocycleOne (α : A) (hα : α + A.ρ c α = 0) :
    cochainOf A (cocycleι A 1 (cocycleOne A hG hc α hα)) = cochainOne A α :=
  congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

end OrderTwo

section OrderTwoClasses

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

include hG hc in

theorem exists_eq_cocycleOne (z : cocycles A 1) :
    ∃ (α : A) (hα : α + A.ρ c α = 0), z = cocycleOne A hG hc α hα := by
  have h11 := cocycle_one A z 1 1
  have hcc := cocycle_one A z c c
  rw [mul_self_eq_one hG hc] at hcc
  simp only [one_mul, map_one, Module.End.one_apply] at h11
  have hw1 : cochainOf A (cocycleι A 1 z) ![1] = 0 := by simpa using h11
  have hα : cochainOf A (cocycleι A 1 z) ![c] + A.ρ c (cochainOf A (cocycleι A 1 z) ![c]) = 0 := by
    rw [hw1, sub_zero] at hcc
    rw [add_comm]
    exact hcc
  refine ⟨_, hα, cocycles_ext ?_⟩
  rw [cochainOf_cocycleOne]
  funext v
  have hv : v = ![v 0] := by funext i; fin_cases i; rfl
  rw [hv]
  rcases hG (v 0) with h0 | h0
  · simp only [h0]
    rw [cochainOne_one]
    exact hw1
  · simp only [h0]
    rw [cochainOne_c A hc]

include hG in

theorem cohomologyπ_cocycleOne_eq_zero_iff (α : A) (hα : α + A.ρ c α = 0) :
    cohomologyπ A 1 (cocycleOne A hG hc α hα) = 0 ↔ ∃ m : A, α = A.ρ c m - m := by
  rw [cohomologyπ_one_eq_zero_iff, cochainOf_cocycleOne]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (cochainOne_c A hc α).symm.trans (hm c)⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m, fun g => ?_⟩
    rcases hG g with rfl | rfl
    · rw [cochainOne_one, map_one, Module.End.one_apply, sub_self]
    · exact cochainOne_c A hc _

end OrderTwoClasses

section Two

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

open Classical in

def cochainTwo (c : G) (a : A) : (Fin 2 → G) → A := fun v => if v 0 = c ∧ v 1 = c then a else 0

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainTwo_cc (a : A) : cochainTwo A c a ![c, c] = a := by
  simp [cochainTwo]

include hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainTwo_one_left (a : A) (g : G) : cochainTwo A c a ![1, g] = 0 := by
  simp [cochainTwo, hc.symm]

include hc in
omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
theorem cochainTwo_one_right (a : A) (g : G) : cochainTwo A c a ![g, 1] = 0 := by
  simp [cochainTwo, hc.symm]

include hG hc in

theorem d_cochainTwo (a : A) (ha : A.ρ c a = a) :
    (cochainsComplex A).d 2 3 (mkCochain A (cochainTwo A c a) (IsLocallyConstant.of_discrete _)) =
      0 := by
  apply cochainOf_injective
  funext v
  have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [hv, cochainOf_d_two, cochainOf_mkCochain, cochainOf_zero, Pi.zero_apply]
  have hcc := mul_self_eq_one hG hc
  rcases hG (v 0) with h0 | h0 <;> rcases hG (v 1) with h1 | h1 <;> rcases hG (v 2) with h2 | h2 <;>
    simp [h0, h1, h2, hcc, cochainTwo_cc, cochainTwo_one_left A hc, cochainTwo_one_right A hc, ha]

def cocycleTwo (a : A) (ha : A.ρ c a = a) : cocycles A 2 :=
  (cochainsComplex A).cyclesMk (mkCochain A (cochainTwo A c a) (IsLocallyConstant.of_discrete _)) 3
    (by simp) (d_cochainTwo A hG hc a ha)

theorem cochainOf_cocycleTwo (a : A) (ha : A.ρ c a = a) :
    cochainOf A (cocycleι A 2 (cocycleTwo A hG hc a ha)) = cochainTwo A c a :=
  congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

include hG in

theorem cohomologyπ_cocycleTwo_eq_zero_iff (a : A) (ha : A.ρ c a = a) :
    cohomologyπ A 2 (cocycleTwo A hG hc a ha) = 0 ↔ ∃ m : A, a = m + A.ρ c m := by
  rw [cohomologyπ_two_eq_zero_iff, cochainOf_cocycleTwo]
  have hcc := mul_self_eq_one hG hc
  constructor
  · rintro ⟨f, hf⟩
    have h11 := hf 1 1
    have hcc' := hf c c
    rw [cochainTwo_one_left A hc] at h11
    simp only [one_mul, map_one, Module.End.one_apply, sub_self, zero_add] at h11
    rw [cochainTwo_cc, hcc, ← h11, sub_zero] at hcc'
    exact ⟨f c, hcc'.trans (add_comm _ _)⟩
  · rintro ⟨m, rfl⟩
    classical
    refine ⟨fun g => if g = 1 then 0 else m, fun g h => ?_⟩
    rcases hG g with hg | hg <;> rcases hG h with hh | hh <;>
      simp [hg, hh, hcc, hc, cochainTwo_cc, cochainTwo_one_left A hc, cochainTwo_one_right A hc,
        add_comm]

include hG hc in

theorem exists_eq_cocycleTwo_of_normalized (z : cocycles A 2)
    (h1 : ∀ g, cochainOf A (cocycleι A 2 z) ![1, g] = 0)
    (h2 : ∀ g, cochainOf A (cocycleι A 2 z) ![g, 1] = 0) :
    ∃ ha : A.ρ c (cochainOf A (cocycleι A 2 z) ![c, c]) = cochainOf A (cocycleι A 2 z) ![c, c],
      z = cocycleTwo A hG hc _ ha := by
  have hcc := mul_self_eq_one hG hc
  have e := cocycle_two A z c c c
  rw [hcc, h1, h2, sub_zero, add_zero, sub_eq_zero] at e
  refine ⟨e, cocycles_ext ?_⟩
  rw [cochainOf_cocycleTwo]
  funext v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]
  rcases hG (v 0) with h0 | h0 <;> rcases hG (v 1) with h1' | h1' <;> rw [h0, h1']
  · rw [h1, cochainTwo_one_left A hc]
  · rw [h1, cochainTwo_one_left A hc]
  · rw [h2, cochainTwo_one_right A hc]
  · rw [cochainTwo_cc]

end Two

section TwoSurj

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] (A : Rep.{0} k G) [IsDiscreteRep A] {c : G}
  (hG : ∀ g : G, g = 1 ∨ g = c) (hc : c ≠ 1)

include hG hc in

theorem exists_cohomologyπ_eq_cocycleTwo (z : cocycles A 2) :
    ∃ (a : A) (ha : A.ρ c a = a), cohomologyπ A 2 z = cohomologyπ A 2 (cocycleTwo A hG hc a ha) := by
  have hcc := mul_self_eq_one hG hc
  set w := cochainOf A (cocycleι A 2 z) with hw
  have e1 : ∀ g, w ![1, g] = w ![1, 1] := fun g => by
    have e := cocycle_two A z 1 1 g
    simp only [one_mul, map_one, Module.End.one_apply] at e
    rw [← hw] at e
    rw [← sub_eq_zero, ← e]
    abel
  have e2 : ∀ g, w ![g, 1] = A.ρ g (w ![1, 1]) := fun g => by
    have e := cocycle_two A z g 1 1
    simp only [mul_one] at e
    rw [← hw] at e
    rw [eq_comm, ← sub_eq_zero, ← e]
    abel
  have e3 := cocycle_two A z c c c
  rw [← hw, hcc, e1 c, e2 c] at e3
  set a := w ![c, c] - A.ρ c (w ![1, 1]) with ha_def
  have ha : A.ρ c a = a := by
    have hρ : A.ρ c (A.ρ c (w ![1, 1])) = w ![1, 1] := by
      rw [← Module.End.mul_apply, ← map_mul, hcc, map_one, Module.End.one_apply]
    rw [ha_def, map_sub, hρ, ← sub_eq_zero, ← e3]
    abel
  refine ⟨a, ha, ?_⟩
  rw [← sub_eq_zero, ← map_sub, cohomologyπ_two_eq_zero_iff]
  refine ⟨fun _ => w ![1, 1], fun g h => ?_⟩
  rw [map_sub, cochainOf_sub, Pi.sub_apply, cochainOf_cocycleTwo, ← hw]
  rcases hG g with hg | hg <;> rcases hG h with hh | hh <;> rw [hg, hh]
  · rw [cochainTwo_one_left A hc, e1, map_one, Module.End.one_apply]; abel
  · rw [cochainTwo_one_left A hc, e1, map_one, Module.End.one_apply]; abel
  · rw [cochainTwo_one_right A hc, e2]; abel
  · rw [cochainTwo_cc, ha_def]; abel

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] [IsDiscreteRep A] in
include hG hc in

theorem norm_apply [Fintype G] (m : A) : A.ρ.norm m = m + A.ρ c m := by
  classical
  have huniv : (Finset.univ : Finset G) = {1, c} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hG g
  rw [Representation.norm, LinearMap.sum_apply, huniv, Finset.sum_pair hc.symm, map_one,
    Module.End.one_apply]

end TwoSurj

end OrderTwo

end GroundTheory.ProfCoh
