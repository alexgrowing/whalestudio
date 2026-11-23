import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Descent
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Trivial

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

def resTrivMor {X Y : Rep.{u} k G} (hX : ∀ (m : N) (x : X), X.ρ m x = x)
    (hY : ∀ (m : N) (y : Y), Y.ρ m y = y) (f : X →ₗ[k] Y) :
    Rep.res N.subtype X ⟶ Rep.res N.subtype Y :=
  Rep.ofHom ⟨f, fun m => by
    ext x
    change f (X.ρ m x) = Y.ρ m (f x)
    rw [hX, hY]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [N.Normal] in
@[simp]
theorem resTrivMor_hom_apply {X Y : Rep.{u} k G} (hX : ∀ (m : N) (x : X), X.ρ m x = x)
    (hY : ∀ (m : N) (y : Y), Y.ρ m y = y) (f : X →ₗ[k] Y) (x : X) :
    (resTrivMor N hX hY f).hom x = f x :=
  rfl

theorem cohomologyMap_comp_cohomologyConj_of_apply {T A : Rep.{u} k G} [IsDiscreteRep T]
    [IsDiscreteRep A] (φ ψ : Rep.res N.subtype T ⟶ Rep.res N.subtype A) (g : G)
    (h : ∀ t : T, A.ρ g (φ.hom t) = ψ.hom (T.ρ g t)) (n : ℕ) :
    cohomologyMap φ n ≫ cohomologyConj A N n g = cohomologyConj T N n g ≫ cohomologyMap ψ n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap,
    cohomologyConj, cohomologyConj, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun t => ?_) n
  exact h t

theorem cohomologyConj_eq_cohomologyMap_of_sum {T A : Rep.{u} k G} [IsDiscreteRep T]
    [IsDiscreteRep A] (hT : ∀ (m : N) (t : T), T.ρ m t = t) (hA : ∀ (m : N) (a : A), A.ρ m a = a)
    {ι : Type} [Fintype ι] (i : ι → (T →ₗ[k] A)) (p : ι → (A →ₗ[k] T))
    (hip : ∑ j, i j ∘ₗ p j = LinearMap.id) (g : G) (hg : ∀ t : T, T.ρ g t = t) (n : ℕ)
    (hconj : cohomologyConj T N n g = 𝟙 _) :
    cohomologyConj A N n g = cohomologyMap (resTrivMor N hA hA (A.ρ g)) n := by
  have hipa : ∀ a : A, ∑ j, i j (p j a) = a := fun a => by
    have := congrArg (fun f : A →ₗ[k] A => f a) hip
    simpa [LinearMap.sum_apply] using this
  have hsum : ∑ j, resTrivMor N hA hT (p j) ≫ resTrivMor N hT hA (i j) = 𝟙 _ := by
    ext a
    rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
    exact hipa a
  have hsum' : ∑ j, resTrivMor N hA hT (p j) ≫ resTrivMor N hT hA (A.ρ g ∘ₗ i j) =
      resTrivMor N hA hA (A.ρ g) := by
    ext a
    rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
    change ∑ j, A.ρ g (i j (p j a)) = A.ρ g a
    rw [← map_sum, hipa]
  have hj : ∀ j, cohomologyMap (resTrivMor N hT hA (i j)) n ≫ cohomologyConj A N n g =
      cohomologyMap (resTrivMor N hT hA (A.ρ g ∘ₗ i j)) n := fun j => by
    rw [cohomologyMap_comp_cohomologyConj_of_apply N _ (resTrivMor N hT hA (A.ρ g ∘ₗ i j)) g
      (fun t => by rw [hg t]; rfl) n, hconj, Category.id_comp]
  calc cohomologyConj A N n g = 𝟙 _ ≫ cohomologyConj A N n g := (Category.id_comp _).symm
    _ = ∑ j, cohomologyMap (resTrivMor N hA hT (p j)) n ≫
          (cohomologyMap (resTrivMor N hT hA (i j)) n ≫ cohomologyConj A N n g) := by
        rw [← cohomologyMap_id, ← hsum, cohomologyMap_sum, Preadditive.sum_comp]
        simp only [cohomologyMap_comp, Category.assoc]
    _ = cohomologyMap (resTrivMor N hA hA (A.ρ g)) n := by
        simp only [hj, ← cohomologyMap_comp]
        rw [← cohomologyMap_sum, hsum']

end Trivial

section Descent

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) [(U : Subgroup G).Normal]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [(U : Subgroup G).Normal] in

theorem sum_quotient_out_apply_eq_zero (A : Rep.{u} k G)
    (hA : ∀ (m : (U : Subgroup G)) (a : A), A.ρ m a = a)
    (hinv : ∀ a : A, (∀ g : G, A.ρ g a = a) → a = 0) (a : A) :
    ∑ c : G ⧸ (U : Subgroup G), A.ρ c.out a = 0 := by
  apply hinv
  intro g
  rw [map_sum]
  have hc : ∀ c : G ⧸ (U : Subgroup G), A.ρ g (A.ρ c.out a) = A.ρ (g • c).out a := by
    intro c
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (U : Subgroup G) (g * c.out)
    have e : (g • c).out = g * c.out * m := by
      rw [← hm]
      congr 1
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [e, map_mul, Module.End.mul_apply, hA m, ← Module.End.mul_apply, ← map_mul]
  simp_rw [hc]
  exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)

theorem subsingleton_cohomology_of_cohomologyConj_eq (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ (m : (U : Subgroup G)) (a : A), A.ρ m a = a)
    (hinv : ∀ a : A, (∀ g : G, A.ρ g a = a) → a = 0)
    (hbij : Function.Bijective fun a : A => (U : Subgroup G).index • a) (n : ℕ)
    (hconj : ∀ g : G, cohomologyConj A (U : Subgroup G) n g =
      cohomologyMap (resTrivMor (U : Subgroup G) hA hA (A.ρ g)) n) :
    Subsingleton (cohomology A n) := by
  have hAU : Function.Bijective fun a : Rep.res (U : Subgroup G).subtype A =>
      (U : Subgroup G).index • a := hbij
  have hzero : ∑ c : G ⧸ (U : Subgroup G), resTrivMor (U : Subgroup G) hA hA (A.ρ c.out) = 0 := by
    ext a
    rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
    exact sum_quotient_out_apply_eq_zero U A hA hinv a
  refine ⟨fun x y => cohomologyRes_injective_of_bijective U A hbij n ?_⟩
  suffices h : ∀ z : cohomology A n, (cohomologyRes A (U : Subgroup G) n).hom z = 0 by
    rw [h x, h y]
  intro z
  set w := (cohomologyRes A (U : Subgroup G) n).hom z
  have hw : ∀ g : G, (cohomologyConj A (U : Subgroup G) n g).hom w = w :=
    cohomologyRes_apply_mem_cohomologyConjInvariants A _ n z
  apply (bijective_nsmul_cohomology (Rep.res (U : Subgroup G).subtype A) _ hAU n).1
  change (U : Subgroup G).index • w = (U : Subgroup G).index • 0
  rw [smul_zero]
  calc (U : Subgroup G).index • w = ∑ c : G ⧸ (U : Subgroup G), w := by
        rw [Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    _ = ∑ c : G ⧸ (U : Subgroup G), (cohomologyConj A (U : Subgroup G) n c.out).hom w := by
        simp only [hw]
    _ = (cohomologyMap (∑ c : G ⧸ (U : Subgroup G),
          resTrivMor (U : Subgroup G) hA hA (A.ρ c.out)) n).hom w := by
        simp only [hconj, cohomologyMap_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
    _ = 0 := by
        rw [hzero, cohomologyMap_zero]
        rfl

theorem subsingleton_cohomology_of_sum {T A : Rep.{u} k G} [IsDiscreteRep T] [IsDiscreteRep A]
    (hT : ∀ (g : G) (t : T), T.ρ g t = t) (hA : ∀ (m : (U : Subgroup G)) (a : A), A.ρ m a = a)
    (hinv : ∀ a : A, (∀ g : G, A.ρ g a = a) → a = 0)
    (hbij : Function.Bijective fun a : A => (U : Subgroup G).index • a)
    {ι : Type} [Fintype ι] (i : ι → (T →ₗ[k] A)) (p : ι → (A →ₗ[k] T))
    (hip : ∑ j, i j ∘ₗ p j = LinearMap.id) (n : ℕ)
    (hconj : ∀ g : G, cohomologyConj T (U : Subgroup G) n g = 𝟙 _) :
    Subsingleton (cohomology A n) :=
  subsingleton_cohomology_of_cohomologyConj_eq U A hA hinv hbij n fun g =>
    cohomologyConj_eq_cohomologyMap_of_sum (U : Subgroup G) (fun m t => hT m t) hA i p hip g
      (hT g) n (hconj g)

end Descent

section InfRes

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

variable [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

theorem subsingleton_cohomology_of_normal (W : Subgroup Γ) [W.Normal] (hW : IsClosed (W : Set Γ))
    (A : Rep.{u} k Γ) [IsDiscreteRep A] (hinv : ∀ a : A, (∀ w : W, A.ρ w a = a) → a = 0) (q : ℕ)
    (hq : ∀ i, 0 < i → i ≤ q → Subsingleton (cohomology (Rep.res W.subtype A) i)) :
    ∀ i ≤ q, Subsingleton (cohomology A i) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have : Subsingleton (ModuleCat.of k A.ρ.invariants) := ⟨fun a b => Subtype.ext <| by
      rw [hinv a (fun w => a.2 w), hinv b (fun w => b.2 w)]⟩
    exact (H0Iso A).toLinearEquiv.toEquiv.subsingleton
  · have hz : ∀ j, 0 < j → j < i → IsZero (cohomology (Rep.res W.subtype A) j) := fun j hj hji =>
      (ModuleCat.isZero_iff_subsingleton).2 (hq j hj (by omega))
    have hex := infRes_exact A W hW (Nat.pos_iff_ne_zero.1 hpos) hz
    have : Subsingleton (A.quotientToInvariants W) := ⟨fun a b => Subtype.ext <| by
      rw [hinv a (fun w => a.2 w), hinv b (fun w => b.2 w)]⟩
    have hs := subsingleton_cohomology_of_subsingleton (A.quotientToInvariants W) i
    have hres := hq i hpos hi
    have hmem : ∀ z : cohomology A i, z = 0 := by
      intro z
      have hk : z ∈ LinearMap.ker (cohomologyRes A W i).hom :=
        LinearMap.mem_ker.2 (Subsingleton.elim _ _)
      rw [← hex.2] at hk
      obtain ⟨y, rfl⟩ := hk
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => by rw [hmem x, hmem y]⟩

end InfRes

end GroundTheory.ProfCoh
