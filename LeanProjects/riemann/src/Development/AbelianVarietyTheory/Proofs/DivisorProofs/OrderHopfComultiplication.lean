import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HopfFn

theorem tensor_eq_zero_of_lift_eq_zero {R K : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {P Q : Type} [CommRing P] [Algebra R P] [CommRing Q] [Algebra R Q] [Module.Flat R P]
    {X Y : Type} [Finite X] [Finite Y] (φ : X → (P →ₐ[R] K)) (ψ : Y → (Q →ₐ[R] K))
    (hφ : ∀ p, (∀ x, φ x p = 0) → p = 0) (hψ : ∀ q, (∀ y, ψ y q = 0) → q = 0)
    (t : P ⊗[R] Q)
    (ht : ∀ x y, Algebra.TensorProduct.lift (φ x) (ψ y) (fun _ _ => .all _ _) t = 0) :
    t = 0 := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  let Φ : P →ₗ[R] (X → K) := LinearMap.pi (fun x => (φ x).toLinearMap)
  let Ψ : Q →ₗ[R] (Y → K) := LinearMap.pi (fun y => (ψ y).toLinearMap)
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    exact hφ p (fun x => congr_fun hp x)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact hψ q (fun y => congr_fun hq y)
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have hfl : Module.Flat R (Y → K) := Module.Flat.trans R K (Y → K)
  let e := (IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K (X → K) (Y → K)).symm.restrictScalars R
  let g := (TensorProduct.piScalarRight K K (X → K) Y).restrictScalars R
  let L : P ⊗[R] Q →ₗ[R] (Y → X → K) :=
    g.toLinearMap ∘ₗ e.toLinearMap ∘ₗ (Φ.rTensor (Y → K)) ∘ₗ (Ψ.lTensor P)
  have hL : Function.Injective L :=
    g.injective.comp (e.injective.comp
      ((Module.Flat.rTensor_preserves_injective_linearMap Φ hΦ).comp
        (Module.Flat.lTensor_preserves_injective_linearMap Ψ hΨ)))
  have he : ∀ (u : X → K) (v : Y → K), e (u ⊗ₜ[R] v) = u ⊗ₜ[K] v := by
    intro u v
    show (IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K (X → K) (Y → K)).symm _ = _
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have key : ∀ s : P ⊗[R] Q, ∀ x y,
      L s y x = Algebra.TensorProduct.lift (φ x) (ψ y) (fun _ _ => .all _ _) s := by
    intro s x y
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul p q =>
      simp only [L, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, he]
      simp [g, Φ, Ψ, mul_comm]
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  apply hL
  rw [map_zero]
  funext y x
  rw [key]
  exact ht x y

end GlobalTheory.HopfFn

namespace GlobalTheory.HopfFn

open Algebra.TensorProduct in
section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {M : Type} [CommGroup M] [Finite M] (O : Subalgebra R (M → K))

def ev (a : M) : O →ₐ[R] K := (Pi.evalAlgHom R (fun _ : M => K) a).comp O.val

def ev2 (a b : M) : O ⊗[R] O →ₐ[R] K :=
  Algebra.TensorProduct.lift (ev O a) (ev O b) (fun _ _ => .all _ _)

omit [IsDomain R] [IsFractionRing R K] [Finite M] in
@[simp] theorem ev_apply (a : M) (f : O) : ev O a f = (f : M → K) a := rfl

omit [IsDomain R] [IsFractionRing R K] [Finite M] in
@[simp] theorem ev2_tmul (a b : M) (f g : O) :
    ev2 O a b (f ⊗ₜ g) = (f : M → K) a * (g : M → K) b := by
  simp [ev2]

omit [IsDomain R] [IsFractionRing R K] [Finite M] in
theorem ev_inj (f g : O) (h : ∀ a, ev O a f = ev O a g) : f = g :=
  Subtype.ext (funext h)

theorem ev2_inj [Module.Flat R O] (s t : O ⊗[R] O) (h : ∀ a b, ev2 O a b s = ev2 O a b t) :
    s = t :=
  sub_eq_zero.mp (tensor_eq_zero_of_lift_eq_zero (ev O) (ev O)
    (fun p hp => ev_inj O p 0 fun a => by rw [hp, map_zero])
    (fun p hp => ev_inj O p 0 fun a => by rw [hp, map_zero]) _
    fun a b => by rw [map_sub]; exact sub_eq_zero.mpr (h a b))

theorem ev3_inj [Module.Flat R O] (s t : O ⊗[R] (O ⊗[R] O))
    (h : ∀ a b c, lift (ev O a) (ev2 O b c) (fun _ _ => .all _ _) s =
      lift (ev O a) (ev2 O b c) (fun _ _ => .all _ _) t) : s = t :=
  sub_eq_zero.mp (tensor_eq_zero_of_lift_eq_zero (ev O) (fun p : M × M => ev2 O p.1 p.2)
    (fun p hp => ev_inj O p 0 fun a => by rw [hp, map_zero])
    (fun q hq => sub_eq_zero.mp (by
      have := ev2_inj O q 0 fun a b => by rw [hq (a, b), map_zero]
      rw [this, sub_zero])) _
    fun a p => by rw [map_sub]; exact sub_eq_zero.mpr (h a p.1 p.2))

variable (hΔ : ∀ f ∈ O, ∃ T : O ⊗[R] O, ∀ a b : M, ev2 O a b T = f (a * b))
  (hε : ∀ f ∈ O, ∃ c : R, algebraMap R K c = f 1)
  (hS : ∀ f ∈ O, (fun a => f a⁻¹) ∈ O)

def comulFun (f : O) : O ⊗[R] O := Classical.choose (hΔ f.1 f.2)

omit [IsDomain R] [IsFractionRing R K] [Finite M] in
theorem comulFun_spec (f : O) (a b : M) :
    ev2 O a b (comulFun O hΔ f) = (f : M → K) (a * b) :=
  Classical.choose_spec (hΔ f.1 f.2) a b

def comul [Module.Flat R O] : O →ₐ[R] O ⊗[R] O where
  toFun := comulFun O hΔ
  map_one' := ev2_inj O _ _ fun a b => by rw [comulFun_spec, map_one]; rfl
  map_mul' f g := ev2_inj O _ _ fun a b => by
    rw [map_mul, comulFun_spec, comulFun_spec, comulFun_spec]; rfl
  map_zero' := ev2_inj O _ _ fun a b => by rw [comulFun_spec, map_zero]; rfl
  map_add' f g := ev2_inj O _ _ fun a b => by
    rw [map_add, comulFun_spec, comulFun_spec, comulFun_spec]; rfl
  commutes' r := ev2_inj O _ _ fun a b => by rw [comulFun_spec, AlgHom.commutes]; rfl

def counitFun (f : O) : R := Classical.choose (hε f.1 f.2)

omit [IsDomain R] [IsFractionRing R K] [Finite M] in
theorem counitFun_spec (f : O) : algebraMap R K (counitFun O hε f) = (f : M → K) 1 :=
  Classical.choose_spec (hε f.1 f.2)

def counit : O →ₐ[R] R where
  toFun := counitFun O hε
  map_one' := IsFractionRing.injective R K (by rw [counitFun_spec, map_one]; rfl)
  map_mul' f g := IsFractionRing.injective R K (by
    rw [counitFun_spec, map_mul, counitFun_spec, counitFun_spec]; rfl)
  map_zero' := IsFractionRing.injective R K (by rw [counitFun_spec, map_zero]; rfl)
  map_add' f g := IsFractionRing.injective R K (by
    rw [counitFun_spec, map_add, counitFun_spec, counitFun_spec]; rfl)
  commutes' r := IsFractionRing.injective R K (by rw [counitFun_spec]; simp)

theorem counit_spec (f : O) : algebraMap R K (counit O hε f) = (f : M → K) 1 :=
  counitFun_spec O hε f

def antipode : O →ₐ[R] O where
  toFun f := ⟨fun a => (f : M → K) a⁻¹, hS f.1 f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [IsDomain R] [IsFractionRing R K] [Finite M] in
@[simp] theorem antipode_apply (f : O) (a : M) :
    ((antipode O hS f : O) : M → K) a = (f : M → K) a⁻¹ := rfl

end
end GlobalTheory.HopfFn

namespace GlobalTheory.HopfFn

open Algebra.TensorProduct in
section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {M : Type} [CommGroup M] [Finite M] (O : Subalgebra R (M → K)) [Module.Flat R O]
  (hΔ : ∀ f ∈ O, ∃ T : O ⊗[R] O, ∀ a b : M, ev2 O a b T = f (a * b))
  (hε : ∀ f ∈ O, ∃ c : R, algebraMap R K c = f 1)
  (hS : ∀ f ∈ O, (fun a => f a⁻¹) ∈ O)

theorem ev2_comul (a b : M) (f : O) : ev2 O a b (comul O hΔ f) = (f : M → K) (a * b) :=
  comulFun_spec O hΔ f a b

theorem coassoc_left (a b c : M) :
    (lift (ev O a) (ev2 O b c) (fun _ _ => .all _ _)).comp
      ((Algebra.TensorProduct.assoc R R R O O O).toAlgHom.comp (map (comul O hΔ) (.id R O)))
    = ev2 O (a * b) c := by
  apply Algebra.TensorProduct.ext'
  intro x y
  have key : ∀ u : O ⊗[R] O, lift (ev O a) (ev2 O b c) (fun _ _ => .all _ _)
      (Algebra.TensorProduct.assoc R R R O O O (u ⊗ₜ y)) = ev2 O a b u * (y : M → K) c := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => simp [ev2]; ring
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv, add_mul]
  simp only [AlgHom.comp_apply, map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.coe_coe, AlgEquiv.coe_algHom]
  rw [key, ev2_comul, ev2_tmul]

theorem coassoc_right (a b c : M) :
    (lift (ev O a) (ev2 O b c) (fun _ _ => .all _ _)).comp (map (.id R O) (comul O hΔ))
    = ev2 O a (b * c) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [AlgHom.comp_apply, map_tmul, AlgHom.id_apply, lift_tmul, ev2_comul, ev2_tmul,
    ev_apply]

theorem coassoc : (Algebra.TensorProduct.assoc R R R O O O).toAlgHom.comp
      ((map (comul O hΔ) (.id R O)).comp (comul O hΔ))
      = (map (.id R O) (comul O hΔ)).comp (comul O hΔ) := by
  apply AlgHom.ext
  intro f
  apply ev3_inj O
  intro a b c
  have h1 := congrArg (fun φ => φ (comul O hΔ f)) (coassoc_left O hΔ a b c)
  have h2 := congrArg (fun φ => φ (comul O hΔ f)) (coassoc_right O hΔ a b c)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom] at h1 h2 ⊢
  rw [h1, h2, ev2_comul, ev2_comul, _root_.mul_assoc]

theorem rTensor_counit : (map (counit O hε) (.id R O)).comp (comul O hΔ)
      = (Algebra.TensorProduct.lid R O).symm := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.lid R O).injective
  simp only [AlgHom.coe_coe, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply, AlgHom.comp_apply]
  apply ev_inj O
  intro a
  have key : (ev O a).comp ((Algebra.TensorProduct.lid R O).toAlgHom.comp
      (map (counit O hε) (.id R O))) = ev2 O 1 a := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_tmul, ev2_tmul]
    rw [map_smul, Algebra.smul_def, counit_spec]
    rfl
  have := congrArg (fun φ => φ (comul O hΔ f)) key
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom] at this
  rw [this, ev2_comul, _root_.one_mul]
  rfl

theorem lTensor_counit : (map (.id R O) (counit O hε)).comp (comul O hΔ)
      = (Algebra.TensorProduct.rid R R O).symm := by
  apply AlgHom.ext
  intro f
  apply (Algebra.TensorProduct.rid R R O).injective
  simp only [AlgHom.coe_coe, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply, AlgHom.comp_apply]
  apply ev_inj O
  intro a
  have key : (ev O a).comp ((Algebra.TensorProduct.rid R R O).toAlgHom.comp
      (map (.id R O) (counit O hε))) = ev2 O a 1 := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgHom.coe_coe, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_tmul, ev2_tmul]
    rw [map_smul, Algebra.smul_def, counit_spec, _root_.mul_comm]
    rfl
  have := congrArg (fun φ => φ (comul O hΔ f)) key
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom] at this
  rw [this, ev2_comul, _root_.mul_one]
  rfl

end
end GlobalTheory.HopfFn

namespace GlobalTheory.HopfFn

open Algebra.TensorProduct in
section
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {M : Type} [CommGroup M] [Finite M] (O : Subalgebra R (M → K)) [Module.Flat R O]
  (hΔ : ∀ f ∈ O, ∃ T : O ⊗[R] O, ∀ a b : M, ev2 O a b T = f (a * b))
  (hε : ∀ f ∈ O, ∃ c : R, algebraMap R K c = f 1)
  (hS : ∀ f ∈ O, (fun a => f a⁻¹) ∈ O)

abbrev bialg : Bialgebra R O :=
  Bialgebra.ofAlgHom (comul O hΔ) (counit O hε) (coassoc O hΔ) (rTensor_counit O hΔ hε)
    (lTensor_counit O hΔ hε)

theorem antipode_left (a : M) :
    (ev O a).comp (lift (antipode O hS) (.id R O) (fun _ _ => .all _ _)) = ev2 O a⁻¹ a := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp

theorem antipode_right (a : M) :
    (ev O a).comp (lift (.id R O) (antipode O hS) (fun _ _ => .all _ _)) = ev2 O a a⁻¹ := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp

abbrev hopf : HopfAlgebra R O :=
  letI := bialg O hΔ hε
  HopfAlgebra.ofAlgHom (antipode O hS)
    (by
      apply AlgHom.ext
      intro f
      apply ev_inj O
      intro a
      have := congrArg (fun φ => φ (comul O hΔ f)) (antipode_left O hS a)
      simp only [AlgHom.comp_apply] at this
      show ev O a (lift (antipode O hS) (.id R O) (fun _ _ => .all _ _) (comul O hΔ f)) =
        ev O a (algebraMap R O (counit O hε f))
      rw [this, ev2_comul, _root_.inv_mul_cancel, AlgHom.commutes, counit_spec])
    (by
      apply AlgHom.ext
      intro f
      apply ev_inj O
      intro a
      have := congrArg (fun φ => φ (comul O hΔ f)) (antipode_right O hS a)
      simp only [AlgHom.comp_apply] at this
      show ev O a (lift (.id R O) (antipode O hS) (fun _ _ => .all _ _) (comul O hΔ f)) =
        ev O a (algebraMap R O (counit O hε f))
      rw [this, ev2_comul, _root_.mul_inv_cancel, AlgHom.commutes, counit_spec])

theorem cocomm : letI := bialg O hΔ hε; IsCocomm R O := by
  letI := bialg O hΔ hε
  constructor
  apply LinearMap.ext
  intro f
  apply ev2_inj O
  intro a b
  have hc : ∀ t : O ⊗[R] O, ev2 O a b (TensorProduct.comm R O O t) = ev2 O b a t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => simp [_root_.mul_comm]
    | add u v hu hv => simp only [map_add, hu, hv]
  show ev2 O a b (TensorProduct.comm R O O (comul O hΔ f)) = ev2 O a b (comul O hΔ f)
  rw [hc, ev2_comul, ev2_comul, _root_.mul_comm]

theorem ev_convMul (a b : M) : letI := bialg O hΔ hε;
    toConv (ev O (a * b)) = toConv (ev O a) * toConv (ev O b) := by
  letI := bialg O hΔ hε
  rw [AlgHom.convMul_def]
  congr 1
  apply AlgHom.ext
  intro f
  have key : (lmul' R).comp (map (ev O a) (ev O b)) = ev2 O a b := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp
  have := congrArg (fun φ => φ (comul O hΔ f)) key
  simp only [AlgHom.comp_apply] at this
  show ev O (a * b) f = (lmul' R) (map (ev O a) (ev O b) (comul O hΔ f))
  rw [this, ev2_comul]
  rfl

end

theorem exists_hopfAlgebra_of_subalgebra_fun : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (M : Type) [CommGroup M] [Finite M] (O : Subalgebra R (M → K)), Module.Finite R O → Module.Projective R O → (∀ f : M → K, ∃ r : R, r ≠ 0 ∧ r • f ∈ O) → (∀ f ∈ O, ∃ T : O ⊗[R] O, ∀ a b : M, Algebra.TensorProduct.lift ((Pi.evalAlgHom R (fun _ : M => K) a).comp O.val) ((Pi.evalAlgHom R (fun _ : M => K) b).comp O.val) (fun _ _ => .all _ _) T = f (a * b)) → (∀ f ∈ O, (fun a => f a⁻¹) ∈ O) → (∀ f ∈ O, ∃ c : R, algebraMap R K c = f 1) → ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra R A) (_ : IsCocomm R A) (io : A ≃ₐ[R] O), ∀ a b : M, toConv (((Pi.evalAlgHom R (fun _ : M => K) (a * b)).comp O.val).comp io.toAlgHom) = toConv (((Pi.evalAlgHom R (fun _ : M => K) a).comp O.val).comp io.toAlgHom) * toConv (((Pi.evalAlgHom R (fun _ : M => K) b).comp O.val).comp io.toAlgHom) := by
  intro R K _ _ _ _ _ M _ _ O _ _ _ hΔ hS hε
  haveI : Module.Flat R O := inferInstance
  letI := bialg O hΔ hε
  letI H := hopf O hΔ hε hS
  refine ⟨O, inferInstance, H, cocomm O hΔ hε, AlgEquiv.refl, fun a b => ?_⟩
  exact ev_convMul O hΔ hε a b

end GlobalTheory.HopfFn
