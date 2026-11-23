import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

theorem cohomologyConj_one (n : ℕ) : cohomologyConj A N n 1 = 𝟙 _ :=
  cohomologyMapAlong_eq_id _ _ (by ext s; simp)
    (fun a => by change A.ρ 1 a = a; simp) n

theorem cohomologyConj_mul (n : ℕ) (g h : G) :
    cohomologyConj A N n (g * h) = cohomologyConj A N n h ≫ cohomologyConj A N n g := by
  rw [cohomologyConj, cohomologyConj, cohomologyConj, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ ?_ (fun a => ?_) n
  · ext s
    simp only [GroundTheory.GroupCoh.coe_conjHom_apply, MonoidHom.coe_comp, Function.comp_apply]
    group
  · change A.ρ (g * h) a = A.ρ g (A.ρ h a)
    rw [map_mul]
    rfl

theorem cohomologyConj_mul_apply (n : ℕ) (g h : G) (x : cohomology (Rep.res N.subtype A) n) :
    (cohomologyConj A N n (g * h)).hom x =
      (cohomologyConj A N n g).hom ((cohomologyConj A N n h).hom x) := by
  rw [cohomologyConj_mul]
  rfl

@[reassoc]
theorem cohomologyConj_naturality {B : Rep.{u} k G} [IsDiscreteRep B] (f : A ⟶ B) (n : ℕ) (g : G) :
    cohomologyMap ((Rep.resFunctor N.subtype).map f) n ≫ cohomologyConj B N n g =
      cohomologyConj A N n g ≫ cohomologyMap ((Rep.resFunctor N.subtype).map f) n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, cohomologyConj, cohomologyConj,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => ?_) n
  exact (Rep.hom_comm_apply f g a).symm

noncomputable def conjShortComplexMor (S : ShortComplex (Rep.{u} k G)) (g : G) :
    (S.map (Rep.resFunctor N.subtype)).map (Rep.resFunctor (GroundTheory.GroupCoh.conjHom N g)) ⟶
      S.map (Rep.resFunctor N.subtype) where
  τ₁ := GroundTheory.GroupCoh.conjMor S.X₁ N g
  τ₂ := GroundTheory.GroupCoh.conjMor S.X₂ N g
  τ₃ := GroundTheory.GroupCoh.conjMor S.X₃ N g
  comm₁₂ := by
    ext a
    exact (Rep.hom_comm_apply S.f g a)
  comm₂₃ := by
    ext a
    exact (Rep.hom_comm_apply S.g g a)

@[reassoc]
theorem δ_comp_cohomologyConj {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (g : G) :
    δ (shortExact_map_res N hS) i j hij ≫ cohomologyConj S.X₁ N j g =
      cohomologyConj S.X₃ N i g ≫ δ (shortExact_map_res N hS) i j hij :=
  δ_comp_cohomologyMapAlong (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (conjShortComplexMor N S g) _ _ i j hij

section CompactSubgroup

variable [CompactSpace N]

theorem cohomologyConj_of_mem (n : ℕ) {m : G} (hm : m ∈ N) : cohomologyConj A N n m = 𝟙 _ := by
  rw [← cohomologyInnerConj_eq_id (Γ := N) n (Rep.res N.subtype A) ⟨m, hm⟩]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => rfl) n

theorem cohomologyConj_eq_of_mk_eq (n : ℕ) {g h : G} (hgh : (g : G ⧸ N) = h) :
    cohomologyConj A N n g = cohomologyConj A N n h := by
  have hm : g⁻¹ * h ∈ N := QuotientGroup.eq.1 hgh
  have : h = g * (g⁻¹ * h) := by group
  rw [this, cohomologyConj_mul, cohomologyConj_of_mem A N n hm, Category.id_comp]

noncomputable def cohomologyConjRep (n : ℕ) :
    Representation k (G ⧸ N) (cohomology (Rep.res N.subtype A) n) where
  toFun q := (cohomologyConj A N n q.out).hom
  map_one' := by
    rw [cohomologyConj_eq_of_mk_eq A N n (h := 1) (by rw [QuotientGroup.out_eq']; rfl),
      cohomologyConj_one]
    rfl
  map_mul' q r := by
    rw [cohomologyConj_eq_of_mk_eq A N n (h := q.out * r.out)
      (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']), cohomologyConj_mul]
    rfl

theorem cohomologyConjRep_mk (n : ℕ) (g : G) (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyConjRep A N n (g : G ⧸ N) x = (cohomologyConj A N n g).hom x := by
  change (cohomologyConj A N n (g : G ⧸ N).out).hom x = _
  rw [cohomologyConj_eq_of_mk_eq A N n (QuotientGroup.out_eq' (g : G ⧸ N))]

theorem mem_cohomologyConjInvariants_iff (n : ℕ) (x : cohomology (Rep.res N.subtype A) n) :
    x ∈ cohomologyConjInvariants A N n ↔ x ∈ (cohomologyConjRep A N n).invariants := by
  refine ⟨fun hx q => ?_, fun hx g => ?_⟩
  · induction q using QuotientGroup.induction_on with
    | H g => rw [cohomologyConjRep_mk]; exact hx g
  · rw [← cohomologyConjRep_mk]
    exact hx _

end CompactSubgroup

section CompactGroup

variable [CompactSpace G]

@[reassoc]
theorem cohomologyRes_comp_cohomologyConj (n : ℕ) (g : G) :
    cohomologyRes A N n ≫ cohomologyConj A N n g = cohomologyRes A N n := by
  conv_rhs => rw [← Category.id_comp (cohomologyRes A N n), ← cohomologyInnerConj_eq_id n A g]
  rw [cohomologyRes, cohomologyConj, cohomologyInnerConj, ← cohomologyMapAlong_comp,
    ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => rfl) n

theorem cohomologyRes_apply_mem_cohomologyConjInvariants (n : ℕ) (x : cohomology A n) :
    (cohomologyRes A N n).hom x ∈ cohomologyConjInvariants A N n := fun g => by
  rw [← ModuleCat.comp_apply, cohomologyRes_comp_cohomologyConj]

end CompactGroup

end GroundTheory.ProfCoh
