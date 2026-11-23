import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShaDescent
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeTwist
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveInvariants
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Representation

universe u

noncomputable section

section Coordinates

variable {k H N : Type*} [CommRing k] [AddCommGroup H] [Module k H] [AddCommGroup N] [Module k N]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι k N)

def coordTensor (i : ι) : TensorProduct k H N →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H (b.coord i)

omit [Fintype ι] in
theorem coordTensor_tmul (i : ι) (y : H) (m : N) : coordTensor b i (y ⊗ₜ[k] m) = b.coord i m • y := by
  simp [coordTensor]

theorem sum_coordTensor_tmul (z : TensorProduct k H N) : ∑ i, coordTensor b i z ⊗ₜ[k] b i = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  | tmul y m =>
    calc ∑ i, coordTensor b i (y ⊗ₜ[k] m) ⊗ₜ[k] b i = ∑ i, y ⊗ₜ[k] (b.repr m i • b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [coordTensor_tmul, TensorProduct.smul_tmul, Module.Basis.coord_apply]
      _ = y ⊗ₜ[k] m := by rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add z w hz hw =>
    simp only [map_add, TensorProduct.add_tmul]
    rw [Finset.sum_add_distrib, hz, hw]

omit [Fintype ι] in

theorem coordTensor_rTensor {X : Type*} [AddCommGroup X] [Module k X] (f : X →ₗ[k] H) (i : ι)
    (w : TensorProduct k X N) : coordTensor b i (f.rTensor N w) = f (coordTensor b i w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => rw [LinearMap.rTensor_tmul, coordTensor_tmul, coordTensor_tmul, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

theorem mem_range_rTensor_iff {X : Type*} [AddCommGroup X] [Module k X] (f : X →ₗ[k] H)
    (z : TensorProduct k H N) :
    z ∈ LinearMap.range (f.rTensor N) ↔ ∀ i, coordTensor b i z ∈ LinearMap.range f := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨coordTensor b i w, (coordTensor_rTensor b f i w).symm⟩
  · intro h
    choose w hw using h
    refine ⟨∑ i, w i ⊗ₜ[k] b i, ?_⟩
    rw [map_sum]
    simp_rw [LinearMap.rTensor_tmul, hw]
    exact sum_coordTensor_tmul b z

end Coordinates

section Twist

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)]
  (Q : Subgroup G) (ψ : ∀ v, Hv v →ₜ* Q) (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hM : ∀ (g : Q) (m : M), M.ρ g m = m) {ιb : Type*} [Fintype ιb] (b : Module.Basis ιb k M)

def resTensorFormMor (f : M →ₗ[k] k) : Rep.res Q.subtype (T ⊗ M) ⟶ Rep.res Q.subtype T :=
  (resTensorIso Q.subtype T M).hom ≫
    tensorFormMor (M := Rep.res Q.subtype M) (Rep.res Q.subtype T) f
      (form_invariant_of_forall_eq (M := Rep.res Q.subtype M) hM f)

theorem cohomologyMap_resTensorFormMor_twistResMap (f : M →ₗ[k] k) (n : ℕ)
    (y : cohomology (Rep.res Q.subtype T) n) (m : M) :
    (cohomologyMap (resTensorFormMor Q T M hM f) n).hom (twistResMap Q T M hM n (y ⊗ₜ[k] m)) = f m • y := by
  rw [twistResMap_tmul, ← ModuleCat.comp_apply, ← cohomologyMap_comp]
  have e : (tensorRightMor (M := Rep.res Q.subtype M) (Rep.res Q.subtype T) m (fun h => hM h m) ≫
      (resTensorIso Q.subtype T M).inv) ≫ resTensorFormMor Q T M hM f = f m • 𝟙 _ := by
    ext t
    change f m • t = f m • t
    rfl
  rw [e, cohomologyMap_smul, cohomologyMap_id]
  rfl

omit [Fintype ιb] in

theorem cohomologyMap_resTensorFormMor_coord_twistResMap (n : ℕ) (i : ιb)
    (z : TensorProduct k (cohomology (Rep.res Q.subtype T) n) M) :
    (cohomologyMap (resTensorFormMor Q T M hM (b.coord i)) n).hom (twistResMap Q T M hM n z) =
      coordTensor b i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y m => rw [cohomologyMap_resTensorFormMor_twistResMap, coordTensor_tmul]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]

theorem twistResMap_mem_shaSubmodule_iff (n : ℕ)
    (z : TensorProduct k (cohomology (Rep.res Q.subtype T) n) M) :
    twistResMap Q T M hM n z ∈ shaSubmodule ψ (Rep.res Q.subtype (T ⊗ M)) n ↔
      ∀ i, coordTensor b i z ∈ shaSubmodule ψ (Rep.res Q.subtype T) n := by
  constructor
  · intro h i
    rw [← cohomologyMap_resTensorFormMor_coord_twistResMap Q T M hM b n i z]
    exact cohomologyMap_mem_shaSubmodule ψ _ h
  · intro h
    rw [← sum_coordTensor_tmul b z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [twistResMap_tmul]
    exact cohomologyMap_mem_shaSubmodule ψ _ (h i)

end Twist

section Descent

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (P : OpenSubgroup G) [(P : Subgroup G).Normal] (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)
  [Module.Finite k M] (hTr : Module.finrank k T = 1) (hP : ((P : Subgroup G).index : k) ≠ 0)

theorem coe_coprimeTwistEquiv (n : ℕ) (x : cohomology M n) :
    haveI := isDiscreteRep_homRep P T M hT hM
    haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
    haveI : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
    twistResEquiv (P : Subgroup G) T (homRep T M) (homRep_ρ_of_mem P T M hT hM) n
        (coprimeTwistEquiv P T M hT hM hTr hP n x) =
      (cohomologyRes (T ⊗ homRep T M) (P : Subgroup G) n).hom
        ((cohomologyMap (evalInv T M hTr) n).hom x) := by
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  rw [← twistInvariantsEquiv_apply]
  simp only [coprimeTwistEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem mem_shaSubmodule_iff_coprimeTwistEquiv {ιb : Type*} [Fintype ιb]
    (b : Module.Basis ιb k (homRep T M)) (n : ℕ) (x : cohomology M n) :
    x ∈ shaSubmodule φ M n ↔
      ∀ i, coordTensor b i (coprimeTwistEquiv P T M hT hM hTr hP n x : TensorProduct k
        (cohomology (Rep.res (P : Subgroup G).subtype T) n) (homRep T M)) ∈
          shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n := by
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))

  have h1 : x ∈ shaSubmodule φ M n ↔
      (cohomologyMap (evalInv T M hTr) n).hom x ∈ shaSubmodule φ (T ⊗ homRep T M) n := by
    refine ⟨cohomologyMap_mem_shaSubmodule φ _, fun h => ?_⟩
    have e : (cohomologyMap (evalMor T M) n).hom ((cohomologyMap (evalInv T M hTr) n).hom x) = x := by
      rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, evalInv_comp_evalMor, cohomologyMap_id]
      rfl
    rw [← e]
    exact cohomologyMap_mem_shaSubmodule φ _ h
  rw [h1, mem_shaSubmodule_iff_cohomologyRes φ P _ (bijective_nsmul_of_ne_zero hP), ← coe_coprimeTwistEquiv P T M hT hM hTr hP n x,
    twistResEquiv_apply]
  exact twistResMap_mem_shaSubmodule_iff (P : Subgroup G) (mackeyFamily P φ) T (homRep T M)
    (homRep_ρ_of_mem P T M hT hM) b n _

include hTr hP in

theorem finrank_shaSubmodule_eq_finrank_invariants (n : ℕ) {X : Type u} [AddCommGroup X] [Module k X]
    (ρX : Representation k (G ⧸ (P : Subgroup G)) X)
    (e : X →ₗ[k] cohomology (Rep.res (P : Subgroup G).subtype T) n)
    (he : ρX.IsIntertwiningMap (cohomologyConjRep T (P : Subgroup G) n) e) (hinj : Function.Injective e)
    (hrange : ∀ y, y ∈ shaSubmodule (mackeyFamily P φ) (Rep.res (P : Subgroup G).subtype T) n ↔
      y ∈ LinearMap.range e) :
    Module.finrank k (shaSubmodule φ M n) = Module.finrank k
      (ρX.tprod (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants := by
  classical
  have := isDiscreteRep_homRep P T M hT hM
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  set σ := quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM)
  set E := coprimeTwistEquiv P T M hT hM hTr hP n
  set R := e.rTensor (homRep T M)
  have hR : (ρX.tprod σ).IsIntertwiningMap ((cohomologyConjRep T (P : Subgroup G) n).tprod σ) R :=
    isIntertwiningMap_rTensor σ he
  have hRinj : Function.Injective R := Module.Flat.rTensor_preserves_injective_linearMap e hinj
  let Ψ : (ρX.tprod σ).invariants →ₗ[k] ((cohomologyConjRep T (P : Subgroup G) n).tprod σ).invariants :=
    R.restrict (mapsTo_invariants hR)
  let Φ : (ρX.tprod σ).invariants →ₗ[k] cohomology M n := E.symm.toLinearMap ∘ₗ Ψ
  have hΦinj : Function.Injective Φ := fun w w' h =>
    Subtype.ext (hRinj (congrArg Subtype.val (E.symm.injective h)))
  let b := Module.Free.chooseBasis k (homRep T M)
  have hrangeΦ : LinearMap.range Φ = shaSubmodule φ M n := by
    ext x
    rw [mem_shaSubmodule_iff_coprimeTwistEquiv φ P T M hT hM hTr hP b n x]
    constructor
    · rintro ⟨w, rfl⟩ i
      have hEw : (E (Φ w) : TensorProduct k (cohomology (Rep.res (P : Subgroup G).subtype T) n)
          (homRep T M)) = R w := by
        change ((E (E.symm (Ψ w)) : _)) = R w
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [hEw, coordTensor_rTensor]
      exact (hrange _).2 ⟨_, rfl⟩
    · intro h
      obtain ⟨w₀, hw₀⟩ := (mem_range_rTensor_iff b e _).2 fun i => (hrange _).1 (h i)
      have hinv : w₀ ∈ (ρX.tprod σ).invariants := fun q => hRinj (by
        rw [hR.isIntertwining, hw₀]
        exact (E x).2 q)
      refine ⟨⟨w₀, hinv⟩, ?_⟩
      change E.symm (Ψ ⟨w₀, hinv⟩) = x
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hw₀
  rw [← hrangeΦ, LinearMap.finrank_range_of_inj hΦinj]

end Descent

end

end GroundTheory.ProfCoh
