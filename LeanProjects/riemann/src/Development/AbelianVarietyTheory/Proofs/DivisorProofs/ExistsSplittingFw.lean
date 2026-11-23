import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.VF : Type := D.VQ

instance Datum.acgVF : AddCommGroup D.VF := inferInstanceAs (AddCommGroup D.VQ)

instance Datum.modQVF : Module ℚ D.VF := inferInstanceAs (Module ℚ D.VQ)

instance Datum.modFVF : Module D.F D.VF :=
  Module.compHom D.VQ ((D.endO.val : D.endO →ₐ[ℚ] Module.End ℚ D.VQ).toRingHom.comp D.actF.toRingHom)

theorem Datum.smul_VF (x : D.F) (v : D.VF) :
    x • v = (((D.actF x : D.endO) : Module.End ℚ D.VQ) (v : D.VQ) : D.VF) := rfl

instance Datum.towerVF : IsScalarTower ℚ D.F D.VF :=
  ⟨fun q x v => by
    show ((D.actF (q • x) : D.endO) : Module.End ℚ D.VQ) v = q • ((D.actF x : D.endO) : Module.End ℚ D.VQ) v
    rw [map_smul]; rfl⟩

def Datum.endFL (g : D.endO) : Module.End D.F D.VF where
  toFun v := ((g : Module.End ℚ D.VQ) v : D.VQ)
  map_add' v w := map_add (g : Module.End ℚ D.VQ) v w
  map_smul' x v := by
    show (g : Module.End ℚ D.VQ) (((D.actF x : D.endO) : Module.End ℚ D.VQ) v) =
      ((D.actF x : D.endO) : Module.End ℚ D.VQ) ((g : Module.End ℚ D.VQ) v)
    have := congrArg (fun k : D.endO => (k : Module.End ℚ D.VQ) v) (D.actF_comm x g)
    exact this.symm

def Datum.endF : D.endO →+* Module.End D.F D.VF where
  toFun := D.endFL
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def Datum.actOFL (b : D.O) : Module.End D.F D.VF where
  toFun v := (D.actQ b (v : D.VQ) : D.VQ)
  map_add' v w := map_add (D.actQ b) v w
  map_smul' x v := by
    show D.actQ b (((D.actF x : D.endO) : Module.End ℚ D.VQ) v) =
      ((D.actF x : D.endO) : Module.End ℚ D.VQ) (D.actQ b v)
    have := (D.mem_endO.1 (D.actF x).2) b
    exact congrArg (fun k : Module.End ℚ D.VQ => k v) this

def Datum.actOF : D.O →+* Module.End D.F D.VF where
  toFun := D.actOFL
  map_one' := by ext v; show D.actQ 1 v = v; rw [map_one]; rfl
  map_mul' a b := by ext v; show D.actQ (a * b) v = D.actQ a (D.actQ b v); rw [map_mul]; rfl
  map_zero' := by ext v; show D.actQ 0 v = 0; rw [map_zero]; rfl
  map_add' a b := by ext v; show D.actQ (a + b) v = D.actQ a v + D.actQ b v; rw [map_add]; rfl

instance Datum.algFw (τ : D.F →+* PadicAlgCl p) : Algebra D.F (GlobalTheory.LKTrip.FwOf τ) := (GlobalTheory.LKTrip.embOf τ).toAlgebra

abbrev Datum.VL (τ : D.F →+* PadicAlgCl p) : Type := GlobalTheory.LKTrip.FwOf τ ⊗[D.F] D.VF

def Datum.endL (τ : D.F →+* PadicAlgCl p) : D.endO →+* Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ) :=
  (Module.End.baseChangeHom D.F (GlobalTheory.LKTrip.FwOf τ) D.VF).toRingHom.comp D.endF

def Datum.actOL (τ : D.F →+* PadicAlgCl p) : D.O →+* Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ) :=
  (Module.End.baseChangeHom D.F (GlobalTheory.LKTrip.FwOf τ) D.VF).toRingHom.comp D.actOF

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.zpL (τ : D.F →+* PadicAlgCl p) : ℤ_[p] →ₐ[ℤ] Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ) :=
  ((algebraMap (GlobalTheory.LKTrip.FwOf τ) (Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ))).comp
    ((algebraMap ℚ_[p] (GlobalTheory.LKTrip.FwOf τ)).comp (algebraMap ℤ_[p] ℚ_[p]))).toIntAlgHom

theorem Datum.zpL_apply (τ : D.F →+* PadicAlgCl p) (s : ℤ_[p]) :
    D.zpL τ s = algebraMap (GlobalTheory.LKTrip.FwOf τ) (Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ))
      (algebraMap ℚ_[p] (GlobalTheory.LKTrip.FwOf τ) (algebraMap ℤ_[p] ℚ_[p] s)) := rfl

theorem Datum.actOL_zpL (τ : D.F →+* PadicAlgCl p) (b : D.O) (s : ℤ_[p]) :
    Commute ((D.actOL τ).toIntAlgHom b) (D.zpL τ s) := by
  rw [D.zpL_apply]
  exact (Algebra.commutes _ _).symm

def Datum.kapL (τ : D.F →+* PadicAlgCl p) : D.O ⊗[ℤ] ℤ_[p] →ₐ[ℤ] Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ) :=
  Algebra.TensorProduct.lift (R := ℤ) (S := ℤ) (D.actOL τ).toIntAlgHom (D.zpL τ) (D.actOL_zpL τ)

def Datum.sigL (τ : D.F →+* PadicAlgCl p) :
    Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End (GlobalTheory.LKTrip.FwOf τ) (D.VL τ) :=
  (D.kapL τ).toRingHom.comp (D.splitP.some.symm : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* D.O ⊗[ℤ] ℤ_[p])

theorem Datum.finrank_VF : Module.finrank D.F D.VF = D.m * D.n := by
  have h1 : Module.finrank ℚ D.VF = D.m * D.n * Module.finrank ℚ D.F := by
    haveI := D.freeLa; haveI := D.finLa
    show Module.finrank ℚ (ℚ ⊗[ℤ] D.La) = _
    rw [Module.finrank_baseChange, D.rankLa]
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  haveI : FiniteDimensional D.F D.VF := Module.Finite.of_restrictScalars_finite ℚ D.F D.VF
  rw [← Module.finrank_mul_finrank ℚ D.F D.VF, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

instance Datum.finVF : FiniteDimensional D.F D.VF :=
  haveI : FiniteDimensional ℚ D.VF := D.finVQ
  Module.Finite.of_restrictScalars_finite ℚ D.F D.VF

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MatUnit

open Module

variable {L U R : Type} [Field L] [AddCommGroup U] [Module L U] [Ring R] {m : ℕ}
  (σ : Matrix (Fin m) (Fin m) R →+* Module.End L U)

theorem sum_single_one : (∑ j : Fin m, Matrix.single j j (1 : R)) = 1 := by
  ext a b
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp [Matrix.single_apply]
  · rw [if_neg h]; refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply]; split_ifs with h'
    · exact absurd (h'.1.symm.trans h'.2) h
    · rfl

theorem E_mul (i j k : Fin m) :
    σ (Matrix.single i j 1) * σ (Matrix.single j k 1) = σ (Matrix.single i k 1) := by
  rw [← map_mul, Matrix.single_mul_single_same, mul_one]

theorem E_mul_ne (i j k l : Fin m) (h : j ≠ k) :
    σ (Matrix.single i j 1) * σ (Matrix.single k l 1) = 0 := by
  rw [← map_mul, Matrix.single_mul_single_of_ne _ _ _ _ h, map_zero]

def corner (i0 : Fin m) : Submodule L U := LinearMap.range (σ (Matrix.single i0 i0 1))

theorem mem_corner {i0 : Fin m} {w : U} : w ∈ corner σ i0 ↔ σ (Matrix.single i0 i0 1) w = w :=
  ⟨fun ⟨u, hu⟩ => by rw [← hu, ← Module.End.mul_apply, E_mul], fun h => ⟨w, h⟩⟩

def cornerEquiv (i0 : Fin m) : U ≃ₗ[L] (Fin m → corner σ i0) where
  toFun u i := ⟨σ (Matrix.single i0 i 1) u, by rw [mem_corner, ← Module.End.mul_apply, E_mul]⟩
  map_add' u v := by ext i; simp
  map_smul' c u := by ext i; simp
  invFun w := ∑ i, σ (Matrix.single i i0 1) (w i)
  left_inv u := by
    show ∑ i, σ (Matrix.single i i0 1) (σ (Matrix.single i0 i 1) u) = u
    rw [show ∑ i, σ (Matrix.single i i0 1) (σ (Matrix.single i0 i 1) u) = ∑ i, σ (Matrix.single i i 1) u from
      Finset.sum_congr rfl fun i _ => by rw [← Module.End.mul_apply, E_mul]]
    rw [← LinearMap.sum_apply, ← map_sum, sum_single_one, map_one, Module.End.one_apply]
  right_inv w := by
    funext j; apply Subtype.ext
    show σ (Matrix.single i0 j 1) (∑ i, σ (Matrix.single i i0 1) (w i)) = w j
    rw [map_sum, Finset.sum_eq_single j]
    · rw [← Module.End.mul_apply, E_mul, (mem_corner σ).1 (w j).2]
    · intro i _ hij
      rw [← Module.End.mul_apply, E_mul_ne _ _ _ _ _ (Ne.symm hij), LinearMap.zero_apply]
    · intro h; exact absurd (Finset.mem_univ j) h

variable {A : Type} [Ring A] (α : A →+* Module.End L U)

theorem mapsTo_corner (hc : ∀ a M, α a * σ M = σ M * α a) (i0 : Fin m) (a : A) :
    ∀ w ∈ corner σ i0, α a w ∈ corner σ i0 := by
  intro w hw
  rw [mem_corner] at hw ⊢
  rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, hw]

def cornerHom (hc : ∀ a M, α a * σ M = σ M * α a) (i0 : Fin m) : A →+* Module.End L (corner σ i0) where
  toFun a := (α a).restrict (p := corner σ i0) (q := corner σ i0) (by intro w hw; exact mapsTo_corner σ α hc i0 a w hw)
  map_one' := by ext w; simp [LinearMap.restrict_apply]
  map_mul' a b := by ext w; simp [LinearMap.restrict_apply]
  map_zero' := by ext w; simp [LinearMap.restrict_apply]
  map_add' a b := by ext w; simp [LinearMap.restrict_apply]

end GlobalTheory.UPel.HT.MatUnit

section Main

open NumberField Matrix

end Main
