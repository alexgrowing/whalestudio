import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

open Matrix Module

noncomputable section

namespace GlobalTheory.CountId

open GlobalTheory.JR

section Map
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']

def mapGl (φ : k →+* k') (Y : Gl r k) : Gl r k' :=
  (Y.1.map φ, fun i => φ (Y.2.1 i), fun i => φ (Y.2.2.1 i), φ Y.2.2.2)

theorem map_mulVec' (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (fun i => φ ((A *ᵥ v) i)) = A.map φ *ᵥ fun i => φ (v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_vecMul' (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (fun i => φ ((v ᵥ* A) i)) = (fun i => φ (v i)) ᵥ* A.map φ := by
  funext i
  simp [Matrix.vecMul, dotProduct, map_sum, map_mul]

theorem map_pow' (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (i : ℕ) :
    (A ^ i).map φ = (A.map φ) ^ i := by
  induction i with
  | zero => simp [Matrix.map_one]
  | succ m ih => rw [pow_succ, pow_succ, Matrix.map_mul, ih]

theorem mapGl_act (φ : k →+* k') (γ : GL (Fin r) k) (Y : Gl r k) :
    mapGl φ (act γ Y) = act (Matrix.GeneralLinearGroup.map φ γ) (mapGl φ Y) := by
  simp only [mapGl, act]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp [Matrix.map_mul, Matrix.GeneralLinearGroup.map]
  · exact map_mulVec' φ _ _
  · simp only
    rw [map_vecMul']
    simp [Matrix.GeneralLinearGroup.map]

theorem mom_mapGl (φ : k →+* k') (Y : Gl r k) (i : ℕ) : mom (mapGl φ Y) i = φ (mom Y i) := by
  simp only [mom, mapGl]
  rw [← map_pow', ← map_mulVec']
  simp [dotProduct, map_sum, map_mul]

theorem inv_mapGl (φ : k →+* k') (Y : Gl r k) : inv (mapGl φ Y) = (inv Y).map φ := by
  simp only [JR.inv, Inv.map, mapGl]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only
    rw [Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_mapGl φ Y i

theorem Cm_mapGl (φ : k →+* k') (Y : Gl r k) : Cm (mapGl φ Y) = (Cm Y).map φ := by
  ext i j
  simp only [Cm, mapGl, Matrix.of_apply, Matrix.map_apply]
  rw [← map_pow', ← map_vecMul']

theorem Bm_mapGl (φ : k →+* k') (Y : Gl r k) : Bm (mapGl φ Y) = (Bm Y).map φ := by
  ext i j
  simp only [Bm, mapGl, Matrix.of_apply, Matrix.map_apply]
  rw [← map_pow', ← map_mulVec']

theorem Inv_map_map {k'' : Type} [CommRing k''] (φ : k →+* k') (ψ : k' →+* k'') (a : Inv r k) :
    (a.map φ).map ψ = a.map (ψ.comp φ) := rfl

theorem Inv_map_injective (φ : k →+* k') (h : Function.Injective φ) :
    Function.Injective (fun a : Inv r k => a.map φ) := by
  intro a b hab
  simp only [Inv.map, Prod.mk.injEq] at hab
  obtain ⟨h1, h2, h3⟩ := hab
  exact Prod.ext (funext fun i => h (congrFun h1 i)) (Prod.ext (funext fun i => h (congrFun h2 i)) (h h3))

end Map

section Bas
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]

def Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) : Gl n E :=
  (LinearMap.toMatrix e e T, fun i => e.repr v i, fun j => l (e j), 0)

def tw (e : Basis (Fin n) E V) (γ : GL (Fin n) E) : Basis (Fin n) E V :=
  e.map (LinearEquiv.ofLinear (Matrix.toLin e e (γ⁻¹ : GL (Fin n) E)) (Matrix.toLin e e (γ : Matrix _ _ E))
    (by rw [← Matrix.toLin_mul]; simp) (by rw [← Matrix.toLin_mul]; simp))

theorem tw_apply (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (j : Fin n) :
    tw e γ j = ∑ i, ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j • e i := by
  simp [tw, Matrix.toLin_self]

theorem repr_tw_apply (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (i j : Fin n) :
    e.repr (tw e γ j) i = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j := by
  rw [tw_apply, Basis.repr_sum_self]

theorem tw_repr (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (y : V) :
    (fun i => (tw e γ).repr y i) = (γ : Matrix (Fin n) (Fin n) E) *ᵥ fun i => e.repr y i := by
  funext i
  show e.repr (Matrix.toLin e e (γ : Matrix (Fin n) (Fin n) E) y) i = _
  rw [← LinearMap.toMatrix_mulVec_repr e e, LinearMap.toMatrix_toLin]

theorem toMatrix_tw_left (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    (tw e γ).toMatrix e = (γ : Matrix (Fin n) (Fin n) E) := by
  ext i j
  rw [Basis.toMatrix_apply, congrFun (tw_repr e γ (e j)) i]
  simp [Basis.repr_self, Finsupp.single_apply, Matrix.mulVec, dotProduct]

theorem toMatrix_tw_right (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    e.toMatrix (tw e γ) = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  ext i j
  rw [Basis.toMatrix_apply, repr_tw_apply]

theorem tw_tw (e : Basis (Fin n) E V) (γ δ : GL (Fin n) E) : tw (tw e γ) δ = tw e (δ * γ) := by
  have key : ∀ (b : Basis (Fin n) E V) (g : GL (Fin n) E) (y : V) (i : Fin n),
      (tw b g).repr y i = ((g : Matrix (Fin n) (Fin n) E) *ᵥ fun i => b.repr y i) i :=
    fun b g y i => congrFun (tw_repr b g y) i
  refine Basis.repr_injective (LinearEquiv.ext fun x => Finsupp.ext fun i => ?_)
  simp only [key, Units.val_mul, Matrix.mulVec_mulVec]

theorem exists_tw (e e' : Basis (Fin n) E V) : ∃ γ : GL (Fin n) E, tw e γ = e' := by
  refine ⟨⟨e'.toMatrix e, e.toMatrix e', Basis.toMatrix_mul_toMatrix_flip e' e,
    Basis.toMatrix_mul_toMatrix_flip e e'⟩,
    Basis.repr_injective (LinearEquiv.ext fun x => Finsupp.ext fun i => ?_)⟩
  rw [congrFun (tw_repr e _ x) i]
  simp [Basis.toMatrix_mulVec_repr]

theorem Yb_tw (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) (γ : GL (Fin n) E) :
    Yb (tw e γ) T v l = act γ (Yb e T v l) := by
  simp only [Yb, act]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (tw e γ) e (tw e γ) e,
      toMatrix_tw_left, toMatrix_tw_right]
  · exact tw_repr e γ v
  · funext j
    simp [tw_apply, map_sum, Matrix.vecMul, dotProduct, mul_comm]

theorem vecMul_pow_Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (l : V →ₗ[E] E) (i : ℕ) (j : Fin n) :
    ((fun j => l (e j)) ᵥ* (LinearMap.toMatrix e e T) ^ i) j = l ((T ^ i) (e j)) := by
  rw [LinearMap.toMatrix_pow]
  simp only [Matrix.vecMul, dotProduct, LinearMap.toMatrix_apply]
  conv_rhs => rw [← e.sum_repr ((T ^ i) (e j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem Cm_Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) :
    Cm (Yb e T v l) = Matrix.of fun i j : Fin n => l ((T ^ (i : ℕ)) (e j)) := by
  ext i j
  simp only [Cm, Yb, Matrix.of_apply]
  exact vecMul_pow_Yb e T l i j

theorem mom_Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) (i : ℕ) :
    mom (Yb e T v l) i = l ((T ^ i) v) := by
  simp only [mom, Yb]
  rw [LinearMap.toMatrix_pow, LinearMap.toMatrix_mulVec_repr]
  conv_rhs => rw [← e.sum_repr ((T ^ i) v)]
  simp only [dotProduct]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

theorem inv_Yb [Module.Finite E V] (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) :
    inv (Yb e T v l) = (fun i : Fin n => T.charpoly.coeff i, fun i : Fin n => l ((T ^ (i : ℕ)) v), 0) := by
  simp only [JR.inv]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [Yb]
    rw [LinearMap.charpoly_toMatrix]
  · funext i
    exact mom_Yb e T v l i

theorem Cm_mul_Bm {k : Type} [CommRing k] (Y : Gl n k) :
    Cm Y * Bm Y = Matrix.of fun i j : Fin n => mom Y ((i : ℕ) + (j : ℕ)) := by
  ext i j
  simp only [Matrix.mul_apply, Cm, Bm, mom, Matrix.of_apply]
  rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rfl

variable (O : Type) [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]

def lat (e : Basis (Fin n) E V) : Submodule O V := Submodule.span O (Set.range e)

variable [IsDomain O] [Module.IsTorsionFree O E]

theorem mem_lat (e : Basis (Fin n) E V) (y : V) :
    y ∈ lat O e ↔ ∀ i, e.repr y i ∈ (algebraMap O E).range := by
  constructor
  · intro hy
    unfold lat at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero => intro i; exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      intro i
      rw [map_add, Finsupp.add_apply]
      exact Subring.add_mem _ (hx i) (hz i)
    | smul a x _ hx =>
      intro i
      rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ ⟨a, rfl⟩ (hx i)
  · intro h
    choose c hc using h
    rw [← e.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hc i, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem lat_fg (e : Basis (Fin n) E V) : (lat O e).FG := Submodule.fg_span (Set.finite_range _)

theorem span_lat (e : Basis (Fin n) E V) : Submodule.span E (lat O e : Set V) = ⊤ := by
  rw [eq_top_iff, ← e.span_eq]
  exact Submodule.span_mono Submodule.subset_span

theorem lat_stable_iff (e : Basis (Fin n) E V) (T : V →ₗ[E] V) :
    (∀ y ∈ lat O e, T y ∈ lat O e) ↔ ∀ i j, LinearMap.toMatrix e e T i j ∈ (algebraMap O E).range := by
  constructor
  · intro h i j
    rw [LinearMap.toMatrix_apply]
    exact (mem_lat O e _).1 (h _ (by unfold lat; exact Submodule.subset_span ⟨j, rfl⟩)) i
  · intro h y hy
    rw [mem_lat] at hy ⊢
    intro i
    rw [← LinearMap.toMatrix_mulVec_repr e e T y]
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hy j)

theorem lat_fun_iff (e : Basis (Fin n) E V) (l : V →ₗ[E] E) :
    (∀ y ∈ lat O e, l y ∈ (algebraMap O E).range) ↔ ∀ j, l (e j) ∈ (algebraMap O E).range := by
  constructor
  · intro h j
    exact h _ (by unfold lat; exact Submodule.subset_span ⟨j, rfl⟩)
  · intro h y hy
    rw [mem_lat] at hy
    rw [← e.sum_repr y, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Subring.mul_mem _ (hy i) (h i)

theorem lat_tw_le_iff (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    lat O (tw e γ) ≤ lat O e ↔
      ∀ i j, ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range := by
  rw [show lat O (tw e γ) = Submodule.span O (Set.range (tw e γ)) from rfl, Submodule.span_le]
  constructor
  · intro h i j
    have hj := (mem_lat O e (tw e γ j)).1 (h ⟨j, rfl⟩) i
    rwa [repr_tw_apply] at hj
  · rintro h _ ⟨j, rfl⟩
    exact (mem_lat O e _).2 fun i => by rw [repr_tw_apply]; exact h i j

theorem lat_tw_eq_iff (e : Basis (Fin n) E V) (γ δ : GL (Fin n) E) :
    lat O (tw e δ) = lat O (tw e γ) ↔
      ∀ i j, ((δ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range ∧
        (((δ * γ⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range := by
  have h1 : tw e δ = tw (tw e γ) (δ * γ⁻¹) := by rw [tw_tw, inv_mul_cancel_right]
  have h2 : tw e γ = tw (tw e δ) (δ * γ⁻¹)⁻¹ := by
    rw [tw_tw, _root_.mul_inv_rev, _root_.inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  rw [le_antisymm_iff]
  constructor
  · rintro ⟨hle, hge⟩ i j
    refine ⟨?_, ?_⟩
    · have hk := (lat_tw_le_iff O (tw e δ) (δ * γ⁻¹)⁻¹).1 (by rw [← h2]; exact hge) i j
      rwa [_root_.inv_inv] at hk
    · exact (lat_tw_le_iff O (tw e γ) (δ * γ⁻¹)).1 (by rw [← h1]; exact hle) i j
  · intro h
    constructor
    · rw [h1]
      exact (lat_tw_le_iff O _ _).2 fun i j => (h i j).2
    · rw [h2]
      exact (lat_tw_le_iff O _ _).2 fun i j => by rw [_root_.inv_inv]; exact (h i j).1

end Bas

end GlobalTheory.CountId
