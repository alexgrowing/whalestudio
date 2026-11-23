import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

@[ext]
structure CrossedProduct {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) where

  ofCoeff ::

  coeff : (L ≃ₐ[K] L) →₀ L

namespace CrossedProduct

variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem val_smul_units (σ : L ≃ₐ[K] L) (x : Lˣ) : ((σ • x : Lˣ) : L) = σ x := rfl

def mulCoeff (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :
    ((L ≃ₐ[K] L) →₀ L) →+ ((L ≃ₐ[K] L) →₀ L) →+ ((L ≃ₐ[K] L) →₀ L) :=
  Finsupp.liftAddHom fun σ =>
    { toFun := fun a => Finsupp.liftAddHom fun τ =>
        (Finsupp.singleAddHom (σ * τ)).comp
          ((AddMonoidHom.mulRight ((f (σ, τ) : Lˣ) : L)).comp
            ((AddMonoidHom.mulLeft a).comp (σ : L →+ L)))
      map_zero' := by
        ext τ b
        simp
      map_add' := fun a b => by
        ext τ c
        simp [add_mul] }

theorem mulCoeff_single_single (σ τ : L ≃ₐ[K] L) (a b : L) :
    mulCoeff f (Finsupp.single σ a) (Finsupp.single τ b) =
      Finsupp.single (σ * τ) (a * σ b * f (σ, τ)) := by
  simp [mulCoeff]

theorem mulCoeff_assoc (hf : IsMulCocycle₂ f) (x y z : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f (mulCoeff f x y) z = mulCoeff f x (mulCoeff f y z) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, AddMonoidHom.add_apply, hy, hy']
  | single τ b =>
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | single ρ c =>
  simp only [mulCoeff_single_single, mul_assoc, AlgEquiv.mul_apply, map_mul]
  congr 1
  have h := congrArg (fun x : Lˣ => (x : L)) (hf σ τ ρ)
  simp only [Units.val_mul, val_smul_units] at h
  linear_combination (a * σ b * σ (τ c)) * h

theorem mulCoeff_smul_left (c : L) (x y : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f (c • x) y = c • mulCoeff f x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
  | single τ b =>
  simp only [Finsupp.smul_single, smul_eq_mul, mulCoeff_single_single, mul_assoc]

theorem mulCoeff_smul_right (c : K) (x y : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f x (c • y) = c • mulCoeff f x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
  | single τ b =>
  simp only [Finsupp.smul_single, mulCoeff_single_single, Algebra.smul_def, map_mul,
    AlgEquiv.commutes]
  congr 1
  ring

theorem one_mulCoeff (hf : IsMulCocycle₂ f) (x : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f (Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L)) x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single τ b =>
  simp only [mulCoeff_single_single, map_one_fst_of_isMulCocycle₂ hf, one_mul,
    AlgEquiv.one_apply]
  rw [mul_right_comm, Units.inv_mul, one_mul]

theorem mulCoeff_one (hf : IsMulCocycle₂ f) (x : (L ≃ₐ[K] L) →₀ L) :
    mulCoeff f x (Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L)) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
  | single σ a =>
  rw [mulCoeff_single_single, map_one_snd_of_isMulCocycle₂ hf σ, mul_one, val_smul_units, mul_assoc,
    ← map_mul, Units.inv_mul, map_one, mul_one]

variable {hf : IsMulCocycle₂ f}

instance : Zero (CrossedProduct hf) := ⟨⟨0⟩⟩
instance : Add (CrossedProduct hf) := ⟨fun x y => ⟨x.coeff + y.coeff⟩⟩
instance : Neg (CrossedProduct hf) := ⟨fun x => ⟨-x.coeff⟩⟩
instance : Sub (CrossedProduct hf) := ⟨fun x y => ⟨x.coeff - y.coeff⟩⟩
instance {R : Type*} [SMulZeroClass R L] : SMul R (CrossedProduct hf) :=
  ⟨fun r x => ⟨r • x.coeff⟩⟩

@[simp] theorem coeff_zero : (0 : CrossedProduct hf).coeff = 0 := rfl
@[simp] theorem coeff_add (x y : CrossedProduct hf) : (x + y).coeff = x.coeff + y.coeff := rfl
@[simp] theorem coeff_neg (x : CrossedProduct hf) : (-x).coeff = -x.coeff := rfl
@[simp] theorem coeff_sub (x y : CrossedProduct hf) : (x - y).coeff = x.coeff - y.coeff := rfl
@[simp] theorem coeff_smul {R : Type*} [SMulZeroClass R L] (r : R) (x : CrossedProduct hf) :
    (r • x).coeff = r • x.coeff := rfl
@[simp] theorem coeff_ofCoeff (a : (L ≃ₐ[K] L) →₀ L) : (ofCoeff a : CrossedProduct hf).coeff = a :=
  rfl

theorem coeff_injective : Function.Injective (coeff : CrossedProduct hf → _) :=
  fun _ _ => CrossedProduct.ext

instance : AddCommGroup (CrossedProduct hf) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

def coeffAddHom : CrossedProduct hf →+ ((L ≃ₐ[K] L) →₀ L) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance {R : Type*} [Semiring R] [Module R L] : Module R (CrossedProduct hf) :=
  Function.Injective.module R coeffAddHom coeff_injective fun _ _ => rfl

instance : IsScalarTower K L (CrossedProduct hf) :=
  ⟨fun c a x => CrossedProduct.ext (smul_assoc c a x.coeff)⟩

def coeffEquiv (R : Type*) [Semiring R] [Module R L] :
    CrossedProduct hf ≃ₗ[R] ((L ≃ₐ[K] L) →₀ L) where
  toFun := coeff
  invFun := ofCoeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem coeffEquiv_apply (R : Type*) [Semiring R] [Module R L] (x : CrossedProduct hf) :
    coeffEquiv R x = x.coeff := rfl

@[simp] theorem coeffEquiv_symm_apply (R : Type*) [Semiring R] [Module R L]
    (a : (L ≃ₐ[K] L) →₀ L) : (coeffEquiv R).symm a = (ofCoeff a : CrossedProduct hf) := rfl

instance : Mul (CrossedProduct hf) := ⟨fun x y => ⟨mulCoeff f x.coeff y.coeff⟩⟩
instance : One (CrossedProduct hf) := ⟨⟨Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L)⟩⟩

theorem coeff_mul (x y : CrossedProduct hf) : (x * y).coeff = mulCoeff f x.coeff y.coeff := rfl

theorem coeff_one :
    (1 : CrossedProduct hf).coeff = Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L) := rfl

instance instRing : Ring (CrossedProduct hf) where
  __ := (inferInstance : AddCommGroup (CrossedProduct hf))
  mul := (· * ·)
  one := 1
  mul_assoc x y z := CrossedProduct.ext (mulCoeff_assoc hf _ _ _)
  one_mul x := CrossedProduct.ext (one_mulCoeff hf _)
  mul_one x := CrossedProduct.ext (mulCoeff_one hf _)
  left_distrib x y z := CrossedProduct.ext (map_add (mulCoeff f x.coeff) _ _)
  right_distrib x y z := CrossedProduct.ext (by
    simp only [coeff_mul, coeff_add, map_add, AddMonoidHom.add_apply])
  zero_mul x := CrossedProduct.ext (by simp only [coeff_mul, coeff_zero, map_zero,
    AddMonoidHom.zero_apply])
  mul_zero x := CrossedProduct.ext (by simp only [coeff_mul, coeff_zero, map_zero])

instance : IsScalarTower L (CrossedProduct hf) (CrossedProduct hf) :=
  ⟨fun a x y => CrossedProduct.ext (mulCoeff_smul_left a x.coeff y.coeff)⟩

instance instAlgebra : Algebra K (CrossedProduct hf) :=
  Algebra.ofModule
    (fun c x y => CrossedProduct.ext (by
      change mulCoeff f (c • x.coeff) y.coeff = c • mulCoeff f x.coeff y.coeff
      rw [← algebraMap_smul L c x.coeff, mulCoeff_smul_left, algebraMap_smul]))
    (fun c x y => CrossedProduct.ext (mulCoeff_smul_right c x.coeff y.coeff))

theorem algebraMap_eq_smul_one' (c : K) :
    algebraMap K (CrossedProduct hf) c = c • 1 := Algebra.algebraMap_eq_smul_one c

def single (σ : L ≃ₐ[K] L) (a : L) : CrossedProduct hf := ⟨Finsupp.single σ a⟩

def u (σ : L ≃ₐ[K] L) : CrossedProduct hf := single σ 1

@[simp] theorem coeff_single (σ : L ≃ₐ[K] L) (a : L) :
    (single σ a : CrossedProduct hf).coeff = Finsupp.single σ a := rfl

@[simp] theorem coeff_u (σ : L ≃ₐ[K] L) : (u σ : CrossedProduct hf).coeff = Finsupp.single σ 1 :=
  rfl

@[simp] theorem single_zero (σ : L ≃ₐ[K] L) : (single σ 0 : CrossedProduct hf) = 0 := by
  ext1; simp

theorem single_add (σ : L ≃ₐ[K] L) (a b : L) :
    (single σ (a + b) : CrossedProduct hf) = single σ a + single σ b := by
  ext1; simp [Finsupp.single_add]

theorem smul_single (c : L) (σ : L ≃ₐ[K] L) (a : L) :
    c • (single σ a : CrossedProduct hf) = single σ (c * a) := by
  ext1; simp

theorem single_eq_smul_u (σ : L ≃ₐ[K] L) (a : L) :
    (single σ a : CrossedProduct hf) = a • u σ := by
  rw [u, smul_single, mul_one]

theorem single_injective (σ : L ≃ₐ[K] L) :
    Function.Injective (single σ : L → CrossedProduct hf) := fun _ _ h =>
  Finsupp.single_injective σ (congrArg coeff h)

@[simp] theorem single_eq_zero {σ : L ≃ₐ[K] L} {a : L} :
    (single σ a : CrossedProduct hf) = 0 ↔ a = 0 := by
  rw [← single_zero σ, (single_injective σ).eq_iff]

theorem single_mul_single (σ τ : L ≃ₐ[K] L) (a b : L) :
    (single σ a : CrossedProduct hf) * single τ b = single (σ * τ) (a * σ b * f (σ, τ)) :=
  CrossedProduct.ext (mulCoeff_single_single σ τ a b)

theorem one_def : (1 : CrossedProduct hf) = single 1 (((f (1, 1))⁻¹ : Lˣ) : L) := rfl

theorem eq_sum_single (x : CrossedProduct hf) :
    x = x.coeff.sum fun σ a => single σ a := by
  apply coeff_injective
  change x.coeff = coeffAddHom (x.coeff.sum fun σ a => single σ a)
  rw [map_finsuppSum]
  exact (Finsupp.sum_single x.coeff).symm

@[elab_as_elim]
theorem induction_on {p : CrossedProduct hf → Prop} (x : CrossedProduct hf) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y)) (single : ∀ σ a, p (single σ a)) : p x := by
  obtain ⟨c⟩ := x
  induction c using Finsupp.induction_linear with
  | zero => exact zero
  | add c d hc hd => exact add ⟨c⟩ ⟨d⟩ hc hd
  | single σ a => exact single σ a

def incl : L →ₐ[K] CrossedProduct hf where
  toFun a := single 1 (a * ((f (1, 1))⁻¹ : Lˣ))
  map_one' := by rw [one_mul]; rfl
  map_mul' a b := by
    rw [single_mul_single, one_mul, AlgEquiv.one_apply]
    congr 1
    have h := Units.inv_mul (f (1, 1))
    linear_combination (-(a * b * ((f (1, 1))⁻¹ : Lˣ))) * h
  map_zero' := by rw [zero_mul, single_zero]
  map_add' a b := by rw [add_mul, single_add]
  commutes' c := by
    rw [algebraMap_eq_smul_one', one_def]
    ext1
    rw [coeff_smul, coeff_single, coeff_single, Finsupp.smul_single, Algebra.smul_def]

theorem incl_apply (a : L) :
    (incl a : CrossedProduct hf) = single 1 (a * ((f (1, 1))⁻¹ : Lˣ)) := rfl

theorem incl_eq_smul_one (a : L) : (incl a : CrossedProduct hf) = a • 1 := by
  rw [incl_apply, one_def, smul_single]

theorem incl_mul (a : L) (x : CrossedProduct hf) : incl a * x = a • x := by
  rw [incl_eq_smul_one, smul_mul_assoc, one_mul]

theorem incl_injective : Function.Injective (incl : L → CrossedProduct hf) := fun a b h => by
  rw [incl_apply, incl_apply] at h
  simpa using single_injective 1 h

instance : Nontrivial (CrossedProduct hf) := (incl_injective (hf := hf)).nontrivial

theorem incl_mul_single (a : L) (σ : L ≃ₐ[K] L) (b : L) :
    (incl a : CrossedProduct hf) * single σ b = single σ (a * b) := by
  rw [incl_mul, smul_single]

theorem incl_mul_u (a : L) (σ : L ≃ₐ[K] L) : (incl a : CrossedProduct hf) * u σ = single σ a := by
  rw [u, incl_mul_single, mul_one]

theorem single_mul_incl (σ : L ≃ₐ[K] L) (a b : L) :
    (single σ a : CrossedProduct hf) * incl b = single σ (a * σ b) := by
  rw [incl_apply, single_mul_single, mul_one, map_one_snd_of_isMulCocycle₂ hf σ, val_smul_units,
    map_mul, mul_assoc, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem u_mul_incl (σ : L ≃ₐ[K] L) (a : L) :
    (u σ : CrossedProduct hf) * incl a = incl (σ a) * u σ := by
  simp only [u]
  rw [single_mul_incl, one_mul, incl_mul_single, mul_one]

theorem u_mul_u (σ τ : L ≃ₐ[K] L) :
    (u σ : CrossedProduct hf) * u τ = incl (f (σ, τ) : L) * u (σ * τ) := by
  simp only [u]
  rw [single_mul_single, map_one, one_mul, one_mul, incl_mul_single, mul_one]

theorem u_one : (u 1 : CrossedProduct hf) = incl (f (1, 1) : L) := by
  rw [incl_apply, Units.mul_inv]; rfl

theorem coeff_mul_incl (x : CrossedProduct hf) (b : L) (σ : L ≃ₐ[K] L) :
    (x * incl b).coeff σ = x.coeff σ * σ b := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp [add_mul, hx, hy]
  | single τ a =>
    rw [single_mul_incl, coeff_single, coeff_single]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]

theorem coeff_incl_mul (b : L) (x : CrossedProduct hf) (σ : L ≃ₐ[K] L) :
    (incl b * x).coeff σ = b * x.coeff σ := by
  rw [incl_mul, coeff_smul, Finsupp.smul_apply, smul_eq_mul]

theorem isUnit_u (σ : L ≃ₐ[K] L) : IsUnit (u σ : CrossedProduct hf) := by
  have h := smul_map_inv_div_map_inv_of_isMulCocycle₂ hf σ
  rw [map_one_snd_of_isMulCocycle₂ hf σ, div_eq_div_iff_mul_eq_mul] at h
  have hr : σ • (f (σ⁻¹, σ) * f (1, 1))⁻¹ * (f (σ, σ⁻¹) * f (1, 1)) = 1 := by
    rw [smul_inv', smul_mul', inv_mul_eq_one, h, mul_comm]
  have hl : (f (σ⁻¹, σ) * f (1, 1))⁻¹ * (f (σ⁻¹, σ) * f (1, 1)) = 1 := inv_mul_cancel _
  refine isUnit_iff_exists.2
    ⟨incl (((f (σ⁻¹, σ) * f (1, 1))⁻¹ : Lˣ) : L) * u σ⁻¹, ?_, ?_⟩
  · rw [← mul_assoc, u_mul_incl, mul_assoc, u_mul_u, mul_inv_cancel, u_one, ← map_mul, ← map_mul,
      ← val_smul_units, ← Units.val_mul, ← Units.val_mul, hr, Units.val_one, map_one]
  · rw [mul_assoc, u_mul_u, inv_mul_cancel, u_one, ← map_mul, ← map_mul, ← Units.val_mul,
      ← Units.val_mul, hl, Units.val_one, map_one]

def basis : Module.Basis (L ≃ₐ[K] L) L (CrossedProduct hf) :=
  (Finsupp.basisSingleOne).map (coeffEquiv L).symm

@[simp] theorem basis_apply (σ : L ≃ₐ[K] L) : (basis σ : CrossedProduct hf) = u σ := by
  rw [basis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  rfl

instance : Module.Free L (CrossedProduct hf) := Module.Free.of_basis basis

instance [FiniteDimensional K L] : Module.Finite L (CrossedProduct hf) :=
  Module.Finite.of_basis basis

instance [FiniteDimensional K L] : FiniteDimensional K (CrossedProduct hf) :=
  Module.Finite.trans L _

theorem finrank_left [FiniteDimensional K L] :
    Module.finrank L (CrossedProduct hf) = Nat.card (L ≃ₐ[K] L) :=
  Module.finrank_eq_nat_card_basis basis

theorem finrank_eq_sq [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K (CrossedProduct hf) = Module.finrank K L ^ 2 := by
  rw [← Module.finrank_mul_finrank K L (CrossedProduct hf), finrank_left,
    IsGalois.card_aut_eq_finrank, sq]

end CrossedProduct

end GroundTheory.Brauer

end
