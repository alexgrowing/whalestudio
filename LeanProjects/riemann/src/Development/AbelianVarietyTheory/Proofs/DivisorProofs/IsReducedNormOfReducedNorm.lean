import Mathlib
import GroundTheory.Brauer.Splitting
import GroundTheory.Brauer.SkolemNoether
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGenMatIsHomogeneous
import Development.AbelianVarietyTheory.Definitions.Divisors.LandherrCSA

noncomputable section

namespace GlobalTheory.Nrd

open scoped TensorProduct

section Def

variable (F C : Type) [Field F] [Ring C] [Algebra F C]

def deg : ℕ := Nat.sqrt (Module.finrank F C)

def IsReducedNormOf (x : C) (a : F) : Prop :=
  ∀ (L : Type) [Field L] (ι : F →+* L) (Ψ : C →+* Matrix (Fin (deg F C)) (Fin (deg F C)) L),
    (∀ c : F, Ψ (algebraMap F C c) = Matrix.scalar (Fin (deg F C)) (ι c)) → (Ψ x).det = ι a

open Classical in

def reducedNorm (x : C) : F :=
  if h : ∃ a, IsReducedNormOf F C x a then Classical.choose h else 0

end Def

theorem det_eq_det_of_semilinear {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] {L : Type} [Field L] (ι : F →+* L) {n : ℕ}
    (Ψ₁ Ψ₂ : C →+* Matrix (Fin n) (Fin n) L)
    (h₁ : ∀ c, Ψ₁ (algebraMap F C c) = Matrix.scalar (Fin n) (ι c))
    (h₂ : ∀ c, Ψ₂ (algebraMap F C c) = Matrix.scalar (Fin n) (ι c)) (x : C) :
    (Ψ₁ x).det = (Ψ₂ x).det := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Matrix.det_fin_zero]
  haveI : NeZero n := ⟨hn.ne'⟩
  letI : Algebra F L := ι.toAlgebra
  have hsc : ∀ c : F, Matrix.scalar (Fin n) (ι c) = algebraMap F (Matrix (Fin n) (Fin n) L) c := by
    intro c
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    rfl
  let f₁ : C →ₐ[F] Matrix (Fin n) (Fin n) L := { Ψ₁ with commutes' := fun c ↦ by simp [h₁, hsc] }
  let f₂ : C →ₐ[F] Matrix (Fin n) (Fin n) L := { Ψ₂ with commutes' := fun c ↦ by simp [h₂, hsc] }
  let g₁ : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) f₁ (fun l y ↦ Algebra.commute_algebraMap_left l _)
  let g₂ : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) f₂ (fun l y ↦ Algebra.commute_algebraMap_left l _)
  obtain ⟨u, hu⟩ := GroundTheory.Brauer.exists_unit_conj g₁ g₂
  have h := hu ((1 : L) ⊗ₜ x)
  have e₁ : g₁ ((1 : L) ⊗ₜ x) = Ψ₁ x := by
    simp only [g₁]; erw [Algebra.TensorProduct.lift_tmul]; simp [f₁]
  have e₂ : g₂ ((1 : L) ⊗ₜ x) = Ψ₂ x := by
    simp only [g₂]; erw [Algebra.TensorProduct.lift_tmul]; simp [f₂]
  rw [e₁, e₂] at h
  rw [h, Matrix.det_units_conj]

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

theorem exists_galois_split : ∃ (E : Type) (_ : Field E) (_ : Algebra F E), FiniteDimensional F E ∧ IsGalois F E ∧
    ∃ Ψ : C →+* Matrix (Fin (deg F C)) (Fin (deg F C)) E,
      (∀ c, Ψ (algebraMap F C c) = Matrix.scalar _ (algebraMap F E c)) ∧ ∀ x, IsUnit (Ψ x) ↔ IsUnit x := by
  obtain ⟨E, _, _, hfin, hgal, n, ⟨φ⟩⟩ := GroundTheory.Brauer.exists_isGalois_splits (K := F) C
  have h : Module.finrank F C = n ^ 2 := by
    have := φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_matrix, Fintype.card_fin,
      Module.finrank_self, mul_one] at this
    rw [this, sq]
  have hd : deg F C = n := by rw [deg, h, Nat.sqrt_eq']
  subst hd
  refine ⟨E, inferInstance, inferInstance, hfin, hgal,
    (φ : E ⊗[F] C →+* _).comp (Algebra.TensorProduct.includeRight : C →ₐ[F] E ⊗[F] C).toRingHom, ?_, ?_⟩
  · intro c
    have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[F] E ⊗[F] C) (algebraMap F C c)
        = algebraMap E (E ⊗[F] C) (algebraMap F E c) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F E (E ⊗[F] C)]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at *
    rw [h1]
    erw [AlgEquiv.commutes]
    ext i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  · intro x
    change IsUnit (φ ((1 : E) ⊗ₜ x)) ↔ IsUnit x
    rw [MulEquiv.isUnit_map φ, GlobalTheory.ReducedNormExists.isUnit_one_tmul_iff]

theorem exists_isReducedNormOf (x : C) : ∃ a, IsReducedNormOf F C x a := by
  obtain ⟨E, _, _, _, _, Ψ, hΨ, -⟩ := exists_galois_split (F := F) (C := C)
  have hfix : (Ψ x).det ∈ (⊥ : IntermediateField F E) := by
    refine (IsGalois.mem_bot_iff_fixed _).mpr fun g ↦ ?_
    have := det_eq_det_of_semilinear (algebraMap F E) Ψ (((g : E →+* E)).mapMatrix.comp Ψ) hΨ
      (fun c ↦ by
        simp only [RingHom.coe_comp, Function.comp_apply, hΨ]
        ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp) x
    have h2 := RingHom.map_det (g : E →+* E) (Ψ x)
    calc g (Ψ x).det = (g : E →+* E) (Ψ x).det := rfl
      _ = _ := h2
      _ = (Ψ x).det := this.symm
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hfix
  refine ⟨a, fun L _ ι Φ hΦ ↦ ?_⟩
  letI : Algebra F L := ι.toAlgebra
  let M := AlgebraicClosure L
  let jE : E →ₐ[F] M := IsAlgClosed.lift
  have hιM : ∀ c : F, algebraMap F M c = algebraMap L M (ι c) := fun c ↦
    IsScalarTower.algebraMap_apply F L M c
  have key := det_eq_det_of_semilinear (algebraMap F M) ((jE : E →+* M).mapMatrix.comp Ψ)
    ((algebraMap L M).mapMatrix.comp Φ)
    (fun c ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, hΨ]
      ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp)
    (fun c ↦ by
      simp only [RingHom.coe_comp, Function.comp_apply, hΦ]
      ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, hιM]; split_ifs <;> simp) x
  simp only [RingHom.coe_comp, Function.comp_apply, ← RingHom.map_det] at key
  rw [← ha] at key
  have : (jE : E →+* M) (algebraMap F E a) = algebraMap L M (ι a) := by
    change jE (algebraMap F E a) = _
    rw [AlgHom.commutes, hιM]
  rw [this] at key
  exact ((algebraMap L M).injective key).symm

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

theorem isReducedNormOf_reducedNorm (x : C) : IsReducedNormOf F C x (reducedNorm F C x) := by
  classical
  have h := exists_isReducedNormOf (F := F) (C := C) x
  unfold reducedNorm
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem det_eq_reducedNorm {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = deg F C)
    {L : Type} [Field L] (ι : F →+* L) (Ψ : C →+* Matrix n n L)
    (hΨ : ∀ c, Ψ (algebraMap F C c) = Matrix.scalar n (ι c)) (x : C) :
    (Ψ x).det = ι (reducedNorm F C x) := by
  let e : n ≃ Fin (deg F C) := Fintype.equivFinOfCardEq hn
  let Ψ' : C →+* Matrix (Fin (deg F C)) (Fin (deg F C)) L :=
    (Matrix.reindexAlgEquiv L L e).toRingEquiv.toRingHom.comp Ψ
  have h := isReducedNormOf_reducedNorm (F := F) (C := C) x L ι Ψ' (fun c ↦ by
    simp only [Ψ', RingHom.coe_comp, Function.comp_apply, hΨ]
    ext i j
    simp [Matrix.reindexAlgEquiv_apply, Matrix.scalar_apply, Matrix.diagonal_apply])
  rw [← h]
  simp [Ψ', Matrix.reindexAlgEquiv_apply, Matrix.det_reindex_self]

theorem reducedNorm_mul (x y : C) :
    reducedNorm F C (x * y) = reducedNorm F C x * reducedNorm F C y := by
  obtain ⟨E, _, _, _, _, Ψ, hΨ, -⟩ := exists_galois_split (F := F) (C := C)
  have hc : Fintype.card (Fin (deg F C)) = deg F C := Fintype.card_fin _
  apply (algebraMap F E).injective
  rw [map_mul, ← det_eq_reducedNorm hc _ Ψ hΨ, ← det_eq_reducedNorm hc _ Ψ hΨ,
    ← det_eq_reducedNorm hc _ Ψ hΨ, map_mul, Matrix.det_mul]

theorem reducedNorm_algebraMap (c : F) :
    reducedNorm F C (algebraMap F C c) = c ^ deg F C := by
  obtain ⟨E, _, _, _, _, Ψ, hΨ, -⟩ := exists_galois_split (F := F) (C := C)
  have hc : Fintype.card (Fin (deg F C)) = deg F C := Fintype.card_fin _
  apply (algebraMap F E).injective
  rw [← det_eq_reducedNorm hc _ Ψ hΨ, hΨ, map_pow]
  simp [Matrix.scalar_apply, Matrix.det_diagonal]

theorem reducedNorm_one : reducedNorm F C 1 = 1 := by
  simpa using reducedNorm_algebraMap (F := F) (C := C) 1

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct
open NumberField

section Inv
variable {F C : Type} [Field F] [NumberField F] [IsCMField F] [Ring C] [Algebra F C]
    [FiniteDimensional F C] [Algebra.IsCentral F C] [IsSimpleRing C]

end Inv

section BaseChange
variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

end BaseChange

end GlobalTheory.Nrd

namespace GlobalTheory.Nrd
open scoped TensorProduct

section Map
variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C]

def reducedNormHom (F C : Type) [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] : C →* F where
  toFun := reducedNorm F C
  map_one' := reducedNorm_one
  map_mul' := reducedNorm_mul

@[simp] theorem reducedNormHom_apply (x : C) : reducedNormHom F C x = reducedNorm F C x := rfl

end Map

end GlobalTheory.Nrd
