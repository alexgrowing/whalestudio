import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneSubOfIsIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorSub

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (X : Representation ℂ G V) (T : Representation ℂ H W)

def up (U : Subrepresentation X) : Subrepresentation (extTensor X T) where
  toSubmodule := LinearMap.range (U.toSubmodule.subtype.rTensor W)
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u w =>
      refine ⟨⟨X g.1 u, U.apply_mem_toSubmodule g.1 u.2⟩ ⊗ₜ T g.2 w, ?_⟩
      simp
    | add x y hx hy =>
      rw [map_add, map_add]; exact add_mem hx hy

def down (S : Subrepresentation (extTensor X T)) : Subrepresentation X where
  toSubmodule :=
    { carrier := {v | ∀ w : W, v ⊗ₜ[ℂ] w ∈ S.toSubmodule}
      add_mem' := fun ha hb w => by rw [TensorProduct.add_tmul]; exact add_mem (ha w) (hb w)
      zero_mem' := fun w => by rw [TensorProduct.zero_tmul]; exact zero_mem _
      smul_mem' := fun c v hv w => by
        rw [← TensorProduct.smul_tmul']; exact S.toSubmodule.smul_mem c (hv w) }
  apply_mem_toSubmodule g v hv w := by
    have := S.apply_mem_toSubmodule (g, 1) (hv w)
    simpa using this

theorem exists_asAlgebraHom_eq {T : Representation ℂ H W} (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1)
    (A : Module.End ℂ W) (s : Finset W) :
    ∃ r : MonoidAlgebra ℂ H, ∀ v ∈ s, T.asAlgebraHom r v = A v := by
  classical
  set R := MonoidAlgebra ℂ H
  have hsimple : IsSimpleModule R T.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule T).1 hirr
  set E := T.asModuleEquiv
  have hsc : ∀ φ : Module.End R T.asModule, ∃ c : ℂ, ∀ x, E (φ x) = c • E x := by
    intro φ
    let B : Module.End ℂ W :=
      { toFun := fun v => E (φ (E.symm v))
        map_add' := fun a b => by simp
        map_smul' := fun c v => by
          rw [RingHom.id_apply, Representation.asModuleEquiv_symm_map_smul, map_smul,
            Representation.asModuleEquiv_map_smul, AlgHom.commutes,
            Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] }
    obtain ⟨c, hc⟩ := hschur B fun m => by
      ext v
      simp only [Module.End.mul_apply, B, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
        Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
        Representation.asAlgebraHom_single_one]
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun F : Module.End ℂ W => F (E x)) hc
    simpa [B] using this
  let f : Module.End (Module.End R T.asModule) T.asModule :=
    { toFun := fun x => E.symm (A (E x))
      map_add' := fun a b => by simp
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        show E.symm (A (E (φ x))) = φ (E.symm (A (E x)))
        apply E.injective
        rw [hc, hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f (s.image E.symm)
  refine ⟨r, fun v hv => ?_⟩
  have := hr (E.symm v) (Finset.mem_image_of_mem _ hv)
  have h2 := congrArg E this
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
  rw [h2, Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]

theorem map_mem (S : Subrepresentation (extTensor X T)) (r : MonoidAlgebra ℂ H) {z : V ⊗[ℂ] W}
    (hz : z ∈ S.toSubmodule) : TensorProduct.map LinearMap.id (T.asAlgebraHom r) z ∈ S.toSubmodule := by
  induction r using MonoidAlgebra.induction_on with
  | of m =>
    have h1 : extTensor X T (1, m) = TensorProduct.map LinearMap.id (T m) :=
      TensorProduct.ext' fun v w => by simp
    rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, ← h1]
    exact S.apply_mem_toSubmodule _ hz
  | add f g hf hg =>
    rw [map_add, TensorProduct.map_add_right, LinearMap.add_apply]
    exact S.toSubmodule.add_mem hf hg
  | smul c f hf =>
    rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]
    exact S.toSubmodule.smul_mem c hf

theorem up_down (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1)
    (S : Subrepresentation (extTensor X T)) : up X T (down X T S) = S := by
  classical
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul u w => simpa using u.2 w
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · intro y hy
    let b := Module.Basis.ofVectorSpace ℂ W
    let F := TensorProduct.equivFinsuppOfBasisRight (M := V) b
    have hy' : y = (F y).sum fun j a => a ⊗ₜ[ℂ] b j := by
      conv_lhs => rw [← F.symm_apply_apply y]
      exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F y)
    have hmem : ∀ j₀, F y j₀ ∈ (down X T S).toSubmodule := by
      intro j₀ w
      by_cases hj₀ : F y j₀ = 0
      · rw [hj₀, TensorProduct.zero_tmul]; exact zero_mem _
      let A : Module.End ℂ W := b.constr ℂ fun j => if j = j₀ then w else 0
      obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hirr hschur A ((F y).support.image b)
      have := map_mem X T S r hy
      rw [hy', map_finsuppSum] at this
      convert this using 1
      rw [Finsupp.sum, Finset.sum_eq_single j₀]
      · rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _
          (Finsupp.mem_support_iff.2 hj₀))]
        simp [A]
      · intro j hj hjj
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _ hj)]
        simp [A, hjj]
      · intro h
        exact absurd (Finsupp.mem_support_iff.2 hj₀) h
    rw [hy', Finsupp.sum]
    exact Submodule.sum_mem _ fun j _ => ⟨⟨F y j, hmem j⟩ ⊗ₜ b j, by simp⟩

theorem down_up [Nontrivial W] (U : Subrepresentation X) : down X T (up X T U) = U := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
      by_contra! h
      exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 h)
    let f : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V φ
    have key : ∀ x, f (U.toSubmodule.subtype.rTensor W x) ∈ U.toSubmodule := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | tmul u w' => simpa [f] using U.toSubmodule.smul_mem (φ w') u.2
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    obtain ⟨x, hx⟩ := hv w
    have h2 := key x
    rw [hx] at h2
    simp only [f, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul] at h2
    exact (U.toSubmodule.smul_mem_iff hφ).1 h2
  · intro hv w
    exact ⟨⟨v, hv⟩ ⊗ₜ w, by simp⟩

def orderIso (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1) :
    Subrepresentation X ≃o Subrepresentation (extTensor X T) :=
  haveI := Model.nontrivial_of_isIrreducible hirr
  { toFun := up X T
    invFun := down X T
    left_inv := down_up X T
    right_inv := up_down X T hirr hschur
    map_rel_iff' := by
      intro U U'
      constructor
      · intro h v hv
        have h1 : v ∈ (down X T (up X T U')).toSubmodule := fun w => h ⟨⟨v, hv⟩ ⊗ₜ w, by simp⟩
        rwa [down_up X T U'] at h1
      · intro h
        rintro _ ⟨x, rfl⟩
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem (up X T U').toSubmodule
        | tmul u w => exact ⟨⟨u, h u.2⟩ ⊗ₜ w, by simp⟩
        | add x y hx hy => rw [map_add]; exact (up X T U').toSubmodule.add_mem hx hy }

def upEquiv (U : Subrepresentation X) :
    (extTensor U.toRepresentation T).Equiv (up X T U).toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.ofInjective (U.toSubmodule.subtype.rTensor W)
      (Module.Flat.rTensor_preserves_injective_linearMap _ U.toSubmodule.injective_subtype)) (fun g => by
    apply TensorProduct.ext'
    intro u w
    apply Subtype.ext
    simp only [Subrepresentation.toRepresentation, MonoidHom.coe_mk, OneHom.coe_mk]
    erw [LinearEquiv.ofInjective_apply]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ U.toSubmodule.injective_subtype)

end GlobalTheory.ExtTensorSub
