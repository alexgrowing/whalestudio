import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
import GroundTheory.ProfiniteCohomology.InflationRestriction.Coinduced
import GroundTheory.ProfiniteCohomology.Bridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Algebra

variable (A : Rep.{u} k G) (N : Subgroup G) [N.Normal]

def tgDiff (y : G → A) (g h : G) : A :=
  A.ρ g (y h) - y (g * h) + y g

def IsCocycleOne (x : N → A) : Prop :=
  ∀ a b : N, x (a * b) = x a + A.ρ a (x b)

structure IsTgLift (x : N → A) (y : G → A) : Prop where
  map_one : y 1 = 0
  mul_right : ∀ (g : G) (n : N), y (g * n) = y g + A.ρ g (x n)
  conj : ∀ (h : G) (n : N),
    A.ρ h (x (GroundTheory.GroupCoh.conjHom N h n)) - x n = A.ρ n (y h) - y h

variable {A N} {x : N → A} {y : G → A}

theorem IsTgLift.mul_left (hy : IsTgLift A N x y) (n : N) (g : G) :
    y (n * g) = A.ρ n (y g) + x n := by
  have e : (n : G) * g = g * (GroundTheory.GroupCoh.conjHom N g n : G) := by
    simp only [GroundTheory.GroupCoh.coe_conjHom_apply]; group
  rw [e, hy.mul_right, ← sub_add_cancel (A.ρ g _) (x n), hy.conj]
  abel

theorem IsTgLift.tgDiff_mul_right (hy : IsTgLift A N x y) (g h : G) (n : N) :
    tgDiff A y g (h * n) = tgDiff A y g h := by
  simp only [tgDiff]
  rw [hy.mul_right, ← mul_assoc, hy.mul_right, map_add, ← Module.End.mul_apply, ← map_mul]
  abel

theorem IsTgLift.tgDiff_mul_left (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (g : G) (n : N)
    (h : G) : tgDiff A y (g * n) h = tgDiff A y g h := by
  simp only [tgDiff]
  have e : g * n * h = g * h * (GroundTheory.GroupCoh.conjHom N h n : G) := by simp; group
  rw [e, hy.mul_right, hy.mul_right]
  have hc := hy.conj h n
  have : A.ρ (g * n) (y h) = A.ρ g (A.ρ n (y h)) := by rw [map_mul]; rfl
  rw [this, show A.ρ n (y h) = y h + (A.ρ h (x (GroundTheory.GroupCoh.conjHom N h n)) - x n) by
    rw [hc]; abel, map_add, map_sub, map_mul (A.ρ) g h, Module.End.mul_apply]
  abel

theorem IsTgLift.tgDiff_mem_invariants (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y)
    (g h : G) (n : N) : A.ρ n (tgDiff A y g h) = tgDiff A y g h := by
  have e1 : tgDiff A y (n * g) h = A.ρ n (tgDiff A y g h) := by
    simp only [tgDiff]
    rw [mul_assoc, hy.mul_left, hy.mul_left, map_mul, Module.End.mul_apply, map_add, map_sub]
    abel
  have e2 : (n : G) * g = g * (GroundTheory.GroupCoh.conjHom N g n : G) := by
    simp only [GroundTheory.GroupCoh.coe_conjHom_apply]; group
  rw [← e1, e2, hy.tgDiff_mul_left hx]

theorem IsTgLift.tgDiff_mul_mul (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (g h : G)
    (m n : N) : tgDiff A y (g * m) (h * n) = tgDiff A y g h := by
  rw [hy.tgDiff_mul_left hx, hy.tgDiff_mul_right]

end Algebra

section Cochains

variable [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{u} k G) [IsDiscreteRep A]
  (N : Subgroup G) [N.Normal]

omit [IsTopologicalGroup G] in

def liftCochain {y : G → A} (hy : IsLocallyConstant y) : locallyConstantCochains A 1 :=
  ⟨fun g => y (g 0), hy.comp_continuous (continuous_apply 0)⟩

theorem isLocallyConstant_tgDiff {y : G → A} (hy : IsLocallyConstant y) :
    IsLocallyConstant fun g : Fin 2 → G => tgDiff A y (g 0) (g 1) := by
  have h1 : IsLocallyConstant fun g : Fin 2 → G => A.ρ (g 0) (y (g 1)) :=
    isLocallyConstant_ρ_apply A (continuous_apply 0) (hy.comp_continuous (continuous_apply 1))
  have h2 : IsLocallyConstant fun g : Fin 2 → G => y (g 0 * g 1) :=
    hy.comp_continuous ((continuous_apply 0).mul (continuous_apply 1))
  have h3 : IsLocallyConstant fun g : Fin 2 → G => y (g 0) :=
    hy.comp_continuous (continuous_apply 0)
  exact (h1.sub h2).add h3

theorem cochainsComplex_d_liftCochain {y : G → A} (hy : IsLocallyConstant y) (g : Fin 2 → G) :
    (((cochainsComplex A).d 1 2).hom (liftCochain A hy)).1 g = tgDiff A y (g 0) (g 1) := by
  rw [cochainsComplex_d_one_apply]
  rfl

variable {A N} {x : N → A} {y : G → A}

omit [IsTopologicalGroup G] [IsDiscreteRep A] in
theorem IsTgLift.tgDiff_out (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (g h : G) :
    tgDiff A y (Quotient.out (g : G ⧸ N)) (Quotient.out (h : G ⧸ N)) = tgDiff A y g h := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N g
  obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N h
  change tgDiff A y (g : G ⧸ N).out (h : G ⧸ N).out = _
  rw [hm, hn, hy.tgDiff_mul_mul hx]

omit [IsTopologicalGroup G] in

noncomputable def tgCochain (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y)
    (hyc : IsLocallyConstant y) : locallyConstantCochains (A.quotientToInvariants N) 2 :=
  ⟨fun c => ⟨tgDiff A y (c 0).out (c 1).out, fun n => hy.tgDiff_mem_invariants hx _ _ n⟩, by
    let q : (Fin 2 → G) → (Fin 2 → G ⧸ N) := Pi.map fun _ => QuotientGroup.mk
    have hq : Topology.IsQuotientMap q :=
      (IsOpenQuotientMap.piMap fun _ => QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
    refine isLocallyConstant_of_comp_isQuotientMap hq ?_
    refine IsLocallyConstant.desc _ Subtype.val ?_ Subtype.val_injective
    have : (Subtype.val ∘ ((fun c : Fin 2 → G ⧸ N => (⟨tgDiff A y (c 0).out (c 1).out,
        fun n => hy.tgDiff_mem_invariants hx _ _ n⟩ :
          Representation.invariants (A.ρ.comp N.subtype))) ∘ q)) =
        fun g : Fin 2 → G => tgDiff A y (g 0) (g 1) := by
      funext g
      exact hy.tgDiff_out hx (g 0) (g 1)
    rw [this]
    exact isLocallyConstant_tgDiff A hyc⟩

variable (A N) in

theorem cochainsMapAlong_mk_injective (n : ℕ) :
    Function.Injective ((cochainsMapAlong (A := A.quotientToInvariants N) (B := A)
      (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f n).hom := by
  intro w w' h
  apply Subtype.ext
  funext c
  have := congrFun (congrArg Subtype.val h) fun i => (c i).out
  have hc : (⇑(QuotientGroup.mk' N) ∘ fun i => (c i).out) = c :=
    funext fun i => QuotientGroup.out_eq' (c i)
  change ((w.1 (⇑(QuotientGroup.mk' N) ∘ fun i => (c i).out)) : A) =
    ((w'.1 (⇑(QuotientGroup.mk' N) ∘ fun i => (c i).out)) : A) at this
  rw [hc] at this
  exact Subtype.ext this

theorem cochainsMapAlong_tgCochain (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y)
    (hyc : IsLocallyConstant y) :
    ((cochainsMapAlong (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N)
      (Rep.ofHom (A.ρ.quotientToInvariants_lift N))).f 2).hom (tgCochain hx hy hyc) =
      ((cochainsComplex A).d 1 2).hom (liftCochain A hyc) := by
  apply Subtype.ext
  funext g
  rw [cochainsComplex_d_liftCochain]
  exact hy.tgDiff_out hx (g 0) (g 1)

theorem cochainsComplex_d_d_apply {B : Rep.{u} k G} [IsDiscreteRep B] (i j l : ℕ)
    (v : (cochainsComplex B).X i) :
    ((cochainsComplex B).d j l).hom (((cochainsComplex B).d i j).hom v) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
  rfl

theorem tgCochain_d (hx : IsCocycleOne A N x) (hy : IsTgLift A N x y) (hyc : IsLocallyConstant y) :
    ((cochainsComplex (A.quotientToInvariants N)).d 2 (2 + 1)).hom (tgCochain hx hy hyc) = 0 := by
  apply cochainsMapAlong_mk_injective A N 3
  rw [map_zero]
  refine (hom_f_d_apply _ 2 3 _).trans ?_
  rw [cochainsMapAlong_tgCochain]
  exact cochainsComplex_d_d_apply 1 2 3 _

end Cochains

section CocycleOf

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {B : Rep.{u} k H}
  [IsDiscreteRep B]

noncomputable def cocycleOf (n : ℕ) (v : locallyConstantCochains B n)
    (hv : ((cochainsComplex B).d n (n + 1)).hom v = 0) : cocycles B n :=
  Classical.choose (exists_iCycles_eq_of_d_eq_zero (cochainsComplex B) n v hv)

theorem iCycles_cocycleOf (n : ℕ) (v : locallyConstantCochains B n)
    (hv : ((cochainsComplex B).d n (n + 1)).hom v = 0) :
    ((cochainsComplex B).iCycles n).hom (cocycleOf n v hv) = v :=
  Classical.choose_spec (exists_iCycles_eq_of_d_eq_zero (cochainsComplex B) n v hv)

theorem cocycleOf_eq_iff (n : ℕ) (v : locallyConstantCochains B n)
    (hv : ((cochainsComplex B).d n (n + 1)).hom v = 0) (z : cocycles B n) :
    cocycleOf n v hv = z ↔ ((cochainsComplex B).iCycles n).hom z = v :=
  ⟨fun h => h ▸ iCycles_cocycleOf n v hv, fun h =>
    iCycles_injective _ n ((iCycles_cocycleOf n v hv).trans h.symm)⟩

theorem cohomologyπ_cocycleOf_eq (n : ℕ) (v v' : locallyConstantCochains B (n + 1))
    (hv : ((cochainsComplex B).d (n + 1) (n + 1 + 1)).hom v = 0)
    (hv' : ((cochainsComplex B).d (n + 1) (n + 1 + 1)).hom v' = 0)
    (w : locallyConstantCochains B n) (hw : ((cochainsComplex B).d n (n + 1)).hom w = v' - v) :
    (cohomologyπ B (n + 1)).hom (cocycleOf (n + 1) v' hv') =
      (cohomologyπ B (n + 1)).hom (cocycleOf (n + 1) v hv) := by
  rw [← sub_eq_zero, ← map_sub]
  refine (homologyπ_succ_eq_zero_iff _ n _).2 ⟨w, ?_⟩
  rw [map_sub, iCycles_cocycleOf, iCycles_cocycleOf]
  exact hw

end CocycleOf

end GroundTheory.ProfCoh
