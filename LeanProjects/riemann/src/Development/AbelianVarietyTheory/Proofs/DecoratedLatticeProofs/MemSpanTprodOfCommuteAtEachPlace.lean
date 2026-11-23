import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.PiTensorCommute

open Module

section General

variable {ι : Type} [Fintype ι] {M : ι → Type} [∀ σ, AddCommGroup (M σ)] [∀ σ, Module ℂ (M σ)]

theorem coord_piTensorProduct {κ : ι → Type} (c : ∀ σ, Basis (κ σ) ℂ (M σ)) (p : ∀ σ, κ σ) :
    (Basis.piTensorProduct c).coord p =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ fun σ => (c σ).coord (p σ)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro m
  simp [Basis.coord_apply, Basis.piTensorProduct_repr_tprod_apply]

theorem eq_zero_of_forall_dualDistrib (x : PiTensorProduct ℂ M)
    (h : ∀ f : ∀ σ, Module.Dual ℂ (M σ),
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) x = 0) : x = 0 := by
  let c := fun σ => Basis.ofVectorSpace ℂ (M σ)
  apply (Basis.piTensorProduct c).repr.injective
  ext p
  have := h (fun σ => (c σ).coord (p σ))
  rw [← coord_piTensorProduct] at this
  simpa [Basis.coord_apply] using this

end General

end GlobalTheory.PiTensorCommute

namespace GlobalTheory.PiTensorCommute

open Module

variable {ι : Type} [Fintype ι]
variable {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

theorem dualDistrib_apply_piTensorHomMap (φ : ∀ σ, Module.Dual ℂ (W σ)) (v : ∀ σ, V σ)
    (z : PiTensorProduct ℂ (fun σ => V σ →ₗ[ℂ] W σ)) :
    PiTensorProduct.dualDistrib
        (PiTensorProduct.tprod ℂ fun σ => φ σ ∘ₗ LinearMap.applyₗ (v σ)) z =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ φ)
        (PiTensorProduct.piTensorHomMap z (PiTensorProduct.tprod ℂ v)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r t => simp
  | add a b ha hb => simp [ha, hb]

theorem piTensorHomMap_eq_zero [∀ τ, FiniteDimensional ℂ (V τ)]
    (z : PiTensorProduct ℂ (fun σ => V σ →ₗ[ℂ] W σ))
    (hz : PiTensorProduct.piTensorHomMap z = 0) : z = 0 := by
  classical
  apply eq_zero_of_forall_dualDistrib
  intro ψ
  let b := fun σ => Module.finBasis ℂ (V σ)
  let χ : ∀ σ, Fin (Module.finrank ℂ (V σ)) → Module.Dual ℂ (W σ) := fun σ j =>
    ψ σ ∘ₗ
      { toFun := fun w => ((b σ).coord j).smulRight w
        map_add' := fun w w' => by ext; simp [smul_add]
        map_smul' := fun c w => by
          ext v
          simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, RingHom.id_apply]
          exact smul_comm _ _ _ }
  have hψ : ψ = fun σ => ∑ j, χ σ j ∘ₗ LinearMap.applyₗ (b σ j) := by
    funext σ
    apply LinearMap.ext
    intro t
    simp only [χ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.applyₗ_apply_apply]
    rw [← map_sum]
    congr 1
    apply LinearMap.ext
    intro v
    simp [Basis.coord_apply]
    simp_rw [← map_smul, ← map_sum, (b σ).sum_repr v]
  rw [hψ, MultilinearMap.map_sum, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro J _
  rw [dualDistrib_apply_piTensorHomMap, hz]
  simp

theorem mem_range_piTensorHomMap [∀ τ, FiniteDimensional ℂ (V τ)]
    (Q : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W) :
    Q ∈ LinearMap.range (PiTensorProduct.piTensorHomMap :
      PiTensorProduct ℂ (fun σ => V σ →ₗ[ℂ] W σ) →ₗ[ℂ] _) := by
  classical
  let b := fun σ => Module.finBasis ℂ (V σ)
  let B := Basis.piTensorProduct b
  have hQ : Q = ∑ J, (B.coord J).smulRight (Q (B J)) := by
    apply B.ext
    intro J'
    simp [Basis.coord_apply, Finsupp.single_apply]
  rw [hQ]
  refine Submodule.sum_mem _ (fun J _ => ?_)
  rw [coord_piTensorProduct]
  generalize Q (B J) = w
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r w =>
    refine ⟨r • PiTensorProduct.tprod ℂ (fun σ => ((b σ).coord (J σ)).smulRight (w σ)), ?_⟩
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp [MultilinearMap.map_smul_univ, smul_smul, mul_comm]
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    refine ⟨a₁ + a₂, ?_⟩
    rw [map_add, ha₁, ha₂]
    ext x
    simp

end GlobalTheory.PiTensorCommute

namespace GlobalTheory.PiTensorCommute

open Module

def commDefect {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (p : (X →ₗ[ℂ] X) × (Y →ₗ[ℂ] Y)) : (X →ₗ[ℂ] Y) →ₗ[ℂ] (X →ₗ[ℂ] Y) where
  toFun t := t ∘ₗ p.1 - p.2 ∘ₗ t
  map_add' a b := by ext; simp; abel
  map_smul' c a := by ext; simp [smul_sub]

theorem commDefect_apply {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (p : (X →ₗ[ℂ] X) × (Y →ₗ[ℂ] Y)) (t : X →ₗ[ℂ] Y) : commDefect p t = t ∘ₗ p.1 - p.2 ∘ₗ t := rfl

variable {ι : Type} [Fintype ι] [hdec : DecidableEq ι]

section Slice

variable {M : ι → Type} [∀ σ, AddCommGroup (M σ)] [∀ σ, Module ℂ (M σ)]

theorem prod_erase_update (ψ : ∀ σ, Module.Dual ℂ (M σ)) (t : ∀ σ, M σ) {i τ : ι} (hi : i ≠ τ)
    (x : M i) :
    ∏ σ ∈ Finset.univ.erase τ, ψ σ (Function.update t i x σ) =
      ψ i x * ∏ σ ∈ (Finset.univ.erase τ).erase i, ψ σ (t σ) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro σ hσ
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]

theorem prod_erase_update_self (ψ : ∀ σ, Module.Dual ℂ (M σ)) (t : ∀ σ, M σ) (τ : ι) (x : M τ) :
    ∏ σ ∈ Finset.univ.erase τ, ψ σ (Function.update t τ x σ) =
      ∏ σ ∈ Finset.univ.erase τ, ψ σ (t σ) := by
  apply Finset.prod_congr rfl
  intro σ hσ
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]

def sliceML (ψ : ∀ σ, Module.Dual ℂ (M σ)) (τ : ι) : MultilinearMap ℂ M (M τ) where
  toFun t := (∏ σ ∈ Finset.univ.erase τ, ψ σ (t σ)) • t τ
  map_update_add' := by
    intro inst t i x y
    obtain rfl : inst = hdec := Subsingleton.elim _ _
    by_cases h : i = τ
    · subst h
      simp only [prod_erase_update_self, Function.update_self, smul_add]
    · rw [prod_erase_update ψ t h, prod_erase_update ψ t h, prod_erase_update ψ t h,
        Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
        Function.update_of_ne (Ne.symm h), map_add, add_mul, add_smul]
  map_update_smul' := by
    intro inst t i c x
    obtain rfl : inst = hdec := Subsingleton.elim _ _
    by_cases h : i = τ
    · subst h
      simp only [prod_erase_update_self, Function.update_self, smul_comm _ c]
    · rw [prod_erase_update ψ t h, prod_erase_update ψ t h,
        Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h), map_smul,
        smul_eq_mul, mul_assoc, mul_smul]

theorem sliceML_apply (ψ : ∀ σ, Module.Dual ℂ (M σ)) (τ : ι) (t : ∀ σ, M σ) :
    sliceML ψ τ t = (∏ σ ∈ Finset.univ.erase τ, ψ σ (t σ)) • t τ := rfl

theorem apply_lift_sliceML (ψ : ∀ σ, Module.Dual ℂ (M σ)) (τ : ι) (χ : Module.Dual ℂ (M τ))
    (y : PiTensorProduct ℂ M) :
    χ (PiTensorProduct.lift (sliceML ψ τ) y) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update ψ τ χ)) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r t =>
    simp only [map_smul, PiTensorProduct.lift.tprod, sliceML_apply, PiTensorProduct.dualDistrib_apply]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
    congr 1
    rw [smul_eq_mul, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro σ hσ
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
  | add a b ha hb => simp [ha, hb]

theorem update_id_apply {N : ι → Type} [∀ σ, AddCommGroup (N σ)] [∀ σ, Module ℂ (N σ)]
    (τ : ι) (f : N τ →ₗ[ℂ] N τ) (t : ∀ σ, N σ) :
    (fun σ => Function.update (fun σ => (LinearMap.id : N σ →ₗ[ℂ] N σ)) τ f σ (t σ)) =
      Function.update t τ (f (t τ)) := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem lift_sliceML_map_update (ψ : ∀ σ, Module.Dual ℂ (M σ)) (τ : ι) (f : M τ →ₗ[ℂ] M τ)
    (y : PiTensorProduct ℂ M) :
    PiTensorProduct.lift (sliceML ψ τ)
        (PiTensorProduct.map (Function.update (fun σ => LinearMap.id) τ f) y) =
      f (PiTensorProduct.lift (sliceML ψ τ) y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r t =>
    simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, update_id_apply,
      sliceML_apply, prod_erase_update_self, Function.update_self]
  | add a b ha hb => simp [ha, hb]

theorem dualDistrib_map (ψ : ∀ σ, Module.Dual ℂ (M σ)) (π : ∀ σ, M σ →ₗ[ℂ] M σ)
    (y : PiTensorProduct ℂ M) :
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ ψ) (PiTensorProduct.map π y) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ fun σ => ψ σ ∘ₗ π σ) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r t => simp
  | add a b ha hb => simp [ha, hb]

end Slice

variable {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

theorem piTensorHomMap_map_update (y : PiTensorProduct ℂ (fun σ => V σ →ₗ[ℂ] W σ)) (τ : ι)
    (p : (V τ →ₗ[ℂ] V τ) × (W τ →ₗ[ℂ] W τ)) :
    PiTensorProduct.piTensorHomMap
        (PiTensorProduct.map (Function.update (fun σ => LinearMap.id) τ (commDefect p)) y) =
      PiTensorProduct.piTensorHomMap y ∘ₗ
          PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) -
        PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2) ∘ₗ
          PiTensorProduct.piTensorHomMap y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r t =>
    simp only [map_smul, PiTensorProduct.map_tprod, update_id_apply,
      PiTensorProduct.piTensorHomMap_tprod_eq_map, LinearMap.smul_comp, LinearMap.comp_smul,
      ← smul_sub]
    congr 1
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp, commDefect_apply]
    have e1 : (fun σ => t σ ∘ₗ Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1 σ) =
        Function.update t τ (t τ ∘ₗ p.1) := by
      funext σ; by_cases h : σ = τ
      · subst h; simp
      · simp [Function.update_of_ne h]
    have e2 : (fun σ => Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2 σ ∘ₗ t σ) =
        Function.update t τ (p.2 ∘ₗ t τ) := by
      funext σ; by_cases h : σ = τ
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [e1, e2]
    exact (PiTensorProduct.mapMultilinear ℂ V W).map_update_sub t τ _ _
  | add a b ha hb =>
    simp only [map_add, ha, hb, LinearMap.add_comp, LinearMap.comp_add]
    abel

end GlobalTheory.PiTensorCommute

namespace GlobalTheory.PiTensorCommute

open Module

theorem mem_span_map_of_commute :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V W : ι → Type) [∀ τ, AddCommGroup (V τ)]
      [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
      [∀ τ, FiniteDimensional ℂ (V τ)] (R : ∀ τ, Set ((V τ →ₗ[ℂ] V τ) × (W τ →ₗ[ℂ] W τ)))
      (Q : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ W),
      (∀ τ, ∀ p ∈ R τ, Q ∘ₗ PiTensorProduct.map
          (Function.update (fun σ => (LinearMap.id : V σ →ₗ[ℂ] V σ)) τ p.1) =
        PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : W σ →ₗ[ℂ] W σ)) τ p.2) ∘ₗ Q) →
      Q ∈ Submodule.span ℂ {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ,
        (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧ T = PiTensorProduct.map t} := by
  intro ι _ _ V W _ _ _ _ _ R Q hQ
  let E := fun σ => V σ →ₗ[ℂ] W σ
  let H : ∀ τ, Submodule ℂ (E τ) := fun τ => ⨅ p ∈ R τ, LinearMap.ker (commDefect p)
  have memH : ∀ τ (t : E τ), t ∈ H τ ↔ ∀ p ∈ R τ, t ∘ₗ p.1 = p.2 ∘ₗ t := by
    intro τ t
    simp only [H, Submodule.mem_iInf, LinearMap.mem_ker]
    exact forall₂_congr fun p _ => sub_eq_zero
  choose g hg using fun τ =>
    LinearMap.exists_leftInverse_of_injective (H τ).subtype (H τ).ker_subtype
  let π : ∀ σ, E σ →ₗ[ℂ] E σ := fun σ => (H σ).subtype ∘ₗ g σ
  have hπmem : ∀ τ t, π τ t ∈ H τ := fun τ t => (g τ t).2
  have hπfix : ∀ τ t, t ∈ H τ → π τ t = t := by
    intro τ t ht
    have := LinearMap.congr_fun (hg τ) ⟨t, ht⟩
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.id_apply] at this
    simp [π, this]
  obtain ⟨y, rfl⟩ := mem_range_piTensorHomMap Q
  have hz : ∀ τ, ∀ p ∈ R τ,
      PiTensorProduct.map (Function.update (fun σ => (LinearMap.id : E σ →ₗ[ℂ] E σ)) τ
        (commDefect p)) y = 0 := by
    intro τ p hp
    apply piTensorHomMap_eq_zero
    rw [piTensorHomMap_map_update, hQ τ p hp, sub_self]
  have OP : ∀ (ψ : ∀ σ, Module.Dual ℂ (E σ)) τ,
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ ψ) y =
        PiTensorProduct.dualDistrib
          (PiTensorProduct.tprod ℂ (Function.update ψ τ (ψ τ ∘ₗ π τ))) y := by
    intro ψ τ
    have hKH : PiTensorProduct.lift (sliceML ψ τ) y ∈ H τ := by
      rw [memH]
      intro p hp
      have := lift_sliceML_map_update ψ τ (commDefect p) y
      rw [hz τ p hp, map_zero, commDefect_apply] at this
      exact (sub_eq_zero.1 this.symm)
    have h1 := apply_lift_sliceML ψ τ (ψ τ) y
    rw [Function.update_eq_self] at h1
    rw [← h1, ← apply_lift_sliceML, LinearMap.comp_apply, hπfix _ _ hKH]
  have TEL : ∀ s : Finset ι, ∀ ψ : ∀ σ, Module.Dual ℂ (E σ),
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ ψ) y =
        PiTensorProduct.dualDistrib
          (PiTensorProduct.tprod ℂ fun σ => if σ ∈ s then ψ σ ∘ₗ π σ else ψ σ) y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro ψ; simp
    | insert τ s hτ ih =>
      intro ψ
      rw [ih ψ, OP _ τ]
      have e : Function.update (fun σ => if σ ∈ s then ψ σ ∘ₗ π σ else ψ σ) τ
          ((if τ ∈ s then ψ τ ∘ₗ π τ else ψ τ) ∘ₗ π τ) =
          fun σ => if σ ∈ insert τ s then ψ σ ∘ₗ π σ else ψ σ := by
        funext σ
        by_cases h : σ = τ
        · subst h; simp [hτ]
        · simp [Function.update_of_ne h, h]
      rw [e]
  have hy : y = PiTensorProduct.map π y := by
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_dualDistrib
    intro ψ
    rw [map_sub, dualDistrib_map, TEL Finset.univ ψ]
    simp
  have key : ∀ x : PiTensorProduct ℂ E,
      PiTensorProduct.piTensorHomMap (PiTensorProduct.map π x) ∈ Submodule.span ℂ
        {T | ∃ t : ∀ τ, V τ →ₗ[ℂ] W τ,
          (∀ τ, ∀ p ∈ R τ, t τ ∘ₗ p.1 = p.2 ∘ₗ t τ) ∧ T = PiTensorProduct.map t} := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r t =>
      rw [map_smul, map_smul, PiTensorProduct.map_tprod, PiTensorProduct.piTensorHomMap_tprod_eq_map]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨fun σ => π σ (t σ), fun τ p hp => (memH τ _).1 (hπmem τ _) p hp, rfl⟩)
    | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  rw [hy]
  exact key y

end GlobalTheory.PiTensorCommute
