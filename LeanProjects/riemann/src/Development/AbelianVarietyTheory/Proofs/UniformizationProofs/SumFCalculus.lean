import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.AdicSum
section
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in

theorem _root_.GlobalTheory.AdicSum.sumI_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥)
    {x : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x s') : s = s' := by
  classical
  obtain ⟨N, hN, hs, -, hconv⟩ := h
  obtain ⟨N', hN', hs', -, hconv'⟩ := h'
  set M := N ⊔ N' with hM
  have hMfg : M.FG := hN.sup hN'
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
  have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
  have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
    intro n
    obtain ⟨S, hS⟩ := hconv n
    obtain ⟨S', hS'⟩ := hconv' n
    have h1 := hS (S ∪ S') Finset.subset_union_left
    have h2 := hS' (S ∪ S') Finset.subset_union_right
    have h3 : s - s' ∈ I ^ n • M := by
      have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
        (Submodule.smul_mono le_rfl le_sup_right h2)
    rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
    obtain ⟨y, hy, hyeq⟩ := h3
    have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
    rwa [← hy']
  have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
    have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
    rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
    exact hpow
  exact sub_eq_zero.mp (congrArg Subtype.val h0)

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in

theorem _root_.GlobalTheory.AdicSum.sumI_map (f : E →ₗ[R] E') {x : Ix → E} {s : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) :
    _root_.GlobalTheory.UT.SumI I (fun i => f (x i)) (f s) := by
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  refine ⟨N.map f, hN.map f, Submodule.mem_map_of_mem hs,
    fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  refine ⟨S, fun T hT => ?_⟩
  rw [← Submodule.map_smul'', ← map_sum, ← map_sub]
  exact Submodule.mem_map_of_mem (hS T hT)

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in

theorem _root_.GlobalTheory.AdicSum.sumI_add {x x' : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x' s') :
    _root_.GlobalTheory.UT.SumI I (fun i => x i + x' i) (s + s') := by
  classical
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  obtain ⟨N', hN', hs', hx', hconv'⟩ := h'
  refine ⟨N ⊔ N', hN.sup hN', Submodule.add_mem_sup hs hs',
    fun i => Submodule.add_mem_sup (hx i) (hx' i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  obtain ⟨S', hS'⟩ := hconv' n
  refine ⟨S ∪ S', fun T hT => ?_⟩
  have e : s + s' - ∑ i ∈ T, (x i + x' i) = (s - ∑ i ∈ T, x i) + (s' - ∑ i ∈ T, x' i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS' T (Finset.union_subset_right hT)))

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in

theorem _root_.GlobalTheory.AdicSum.sumI_comp_iff {Jx : Type} {e : Jx → Ix}
    (he : Function.Injective e) {x : Ix → E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) {s : E} :
    _root_.GlobalTheory.UT.SumI I (x ∘ e) s ↔ _root_.GlobalTheory.UT.SumI I x s := by
  classical
  constructor
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun i => ?_, fun n => ?_⟩
    · by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        exact hx j
      · rw [h0 i hi]
        exact N.zero_mem
    · obtain ⟨S, hS⟩ := hconv n
      refine ⟨S.map ⟨e, he⟩, fun T hT => ?_⟩
      rw [← Finset.sum_preimage e T he.injOn x (fun i _ hi => h0 i hi)]
      refine hS _ fun j hj => ?_
      rw [Finset.mem_preimage]
      exact hT (Finset.mem_map_of_mem _ hj)
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun j => hx (e j), fun n => ?_⟩
    obtain ⟨S, hS⟩ := hconv n
    refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
    have hpre : (T.map ⟨e, he⟩ ∪ S).preimage e he.injOn = T := by
      ext j
      simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, he.eq_iff, exists_eq_right]
      exact ⟨fun hj => hj.elim id fun hj => hT (Finset.mem_preimage.mpr hj), Or.inl⟩
    have hsum := hS (T.map ⟨e, he⟩ ∪ S) Finset.subset_union_right
    rw [← Finset.sum_preimage e _ he.injOn x (fun i _ hi => h0 i hi), hpre] at hsum
    exact hsum

end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AdicSum.sumF_calculus : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R),
    _root_.ReciprocityTheory.ChartRestriction.G.Out.AdmBase R I → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Ix : Type)
    (x x' : Ix → F) (s s' : F),
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x s' →
      s = s') ∧
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x' s' →
      ∀ c : F, _root_.GlobalTheory.UT.SumF I F (fun i => c * x i + x' i) (c * s + s')) ∧
    ∀ (Jx : Type) (e : Jx → Ix), Function.Injective e → (∀ i, i ∉ Set.range e → x i = 0) →
      (_root_.GlobalTheory.UT.SumF I F (x ∘ e) s ↔
        _root_.GlobalTheory.UT.SumF I F x s) := by
  intro R _ _ I hadm F _ _ Ix x x' s s'
  obtain ⟨hnoeth, -, -, hcomplete⟩ := hadm
  haveI := hnoeth
  haveI := hcomplete
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  refine ⟨fun h h' => _root_.GlobalTheory.AdicSum.sumI_unique (IsAdicComplete.le_jacobson_bot I) h h',
    fun h h' c => ?_, fun Jx e he h0 => _root_.GlobalTheory.AdicSum.sumI_comp_iff he h0⟩
  let f : F →ₗ[R] F :=
    { toFun := fun y => c * y
      map_add' := mul_add c
      map_smul' := fun r y => by
        show c * (algebraMap R (FractionRing R) r • y) = algebraMap R (FractionRing R) r • (c * y)
        exact Algebra.mul_smul_comm _ _ _ }
  exact _root_.GlobalTheory.AdicSum.sumI_add (_root_.GlobalTheory.AdicSum.sumI_map f h) h'

end GlobalTheory.AdicSum
