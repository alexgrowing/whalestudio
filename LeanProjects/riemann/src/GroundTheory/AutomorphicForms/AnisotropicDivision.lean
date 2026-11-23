import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicRestrict
import GroundTheory.AutomorphicForms.AnisotropicHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]

section General

variable {A : Type*} [Ring A] [Algebra K A] (b : Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

theorem lmat_mul_rmat (a x : R ⊗[K] A) : lmat b R a * rmat b R x = rmat b R x * lmat b R a := by
  ext k l
  have h1 : (lmat b R a * rmat b R x) k = lmat b R a k ᵥ* rmat b R x := by
    funext l
    simp [Matrix.mul_apply, vecMul, dotProduct]
  have h2 : (rmat b R x * lmat b R a) k = rmat b R x k ᵥ* lmat b R a := by
    funext l
    simp [Matrix.mul_apply, vecMul, dotProduct]
  rw [h1, h2]
  simp only [lmat, rmat]
  rw [← coords_mul, ← coords_mul_left, mul_assoc]

variable {R}

theorem coords_symm_baseMap (f : R →ₐ[K] R') (y : κ → R) :
    (coords b R').symm (f ∘ y) = baseMap f ((coords b R).symm y) := by
  apply (coords b R').injective
  rw [LinearEquiv.apply_symm_apply, coords_baseMap, LinearEquiv.apply_symm_apply]

theorem lmat_baseMap (f : R →ₐ[K] R') (a : R ⊗[K] A) :
    lmat b R' (baseMap f a) = (lmat b R a).map f := by
  ext k l
  simp only [lmat, Matrix.map_apply, ← baseMap_baseBasis b f k, ← map_mul, coords_baseMap,
    Function.comp_apply]

variable (R)

def normCoords (y : κ → R) : Fin 1 → R := fun _ => (rmat b R ((coords b R).symm y)).det

theorem normCoords_smul (t : R) (y : κ → R) :
    normCoords b R (t • y) = t ^ Fintype.card κ • normCoords b R y := by
  funext i
  simp only [normCoords, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← rmatHom_apply, map_smul, rmatHom_apply, det_smul]

variable {R}

theorem normCoords_comp (f : R →ₐ[K] R') (y : κ → R) :
    normCoords b R' (f ∘ y) = f ∘ normCoords b R y := by
  funext i
  simp only [normCoords, Function.comp_apply, coords_symm_baseMap, rmat_baseMap]
  rw [AlgHom.map_det]
  rfl

def normPoly (i : Fin 1) : MvPolynomial κ K :=
  normCoords b (MvPolynomial κ K) MvPolynomial.X i

theorem aeval_normPoly (y : κ → R) (i : Fin 1) :
    MvPolynomial.aeval y (normPoly b i) = normCoords b R y i := by
  have h := congrFun (normCoords_comp b (MvPolynomial.aeval y) MvPolynomial.X) i
  have hy : (MvPolynomial.aeval y : MvPolynomial κ K →ₐ[K] R) ∘ MvPolynomial.X = y := by
    funext p
    simp
  rw [hy] at h
  exact h.symm

end General

section Division

variable [NumberField K] {D : Type*} [DivisionRing D] [Algebra K D] {d : ℕ} (b : Basis (Fin d) K D)

def rmatUnits (R : Type*) [CommRing R] [Algebra K R] : (R ⊗[K] D)ˣ →* GL (Fin d) R :=
  Units.map (rmatHom b R : R ⊗[K] D →ₐ[R] Matrix (Fin d) (Fin d) R).toRingHom.toMonoidHom

theorem rmatUnits_val (R : Type*) [CommRing R] [Algebra K R] (x : (R ⊗[K] D)ˣ) :
    (rmatUnits b R x : Matrix (Fin d) (Fin d) R) = rmat b R x := rfl

def normOneUnits : Subgroup (𝔸[K] ⊗[K] D)ˣ :=
  (Reduction.normOneGL K d).comap (rmatUnits b 𝔸[K])

theorem mem_normOneUnits {x : (𝔸[K] ⊗[K] D)ˣ} :
    x ∈ normOneUnits b ↔ rmatUnits b 𝔸[K] x ∈ Reduction.normOneGL K d := Iff.rfl

theorem isUnit_of_ne_zero' {ξ : K ⊗[K] D} (h : ξ ≠ 0) : IsUnit ξ := by
  have h1 : Algebra.TensorProduct.lid K D ξ ≠ 0 :=
    (map_ne_zero_iff _ (Algebra.TensorProduct.lid K D).injective).2 h
  have h2 := (isUnit_iff_ne_zero.2 h1).map (Algebra.TensorProduct.lid K D).symm
  simpa using h2

theorem det_rmat_ne_zero {ξ : K ⊗[K] D} (h : ξ ≠ 0) : (rmat b K ξ).det ≠ 0 := by
  obtain ⟨u, rfl⟩ := isUnit_of_ne_zero' h
  have : (rmat b K u).det * (rmat b K ↑u⁻¹).det = 1 := by
    rw [← det_mul, ← rmat_mul, u.mul_inv, rmat_one, det_one]
  exact left_ne_zero_of_mul_eq_one this

theorem pos_of_basis (b' : Basis (Fin d) K D) : 0 < d := by
  refine Nat.pos_of_ne_zero fun h => ?_
  subst h
  exact one_ne_zero (b'.ext_elem fun i => i.elim0 : (1 : D) = 0)

theorem normCoords_vecMul (x : (𝔸[K] ⊗[K] D)ˣ) (ξv : Fin d → K) :
    normCoords b 𝔸[K] (Reduction.ratVec ξv ᵥ* rmat b 𝔸[K] x) =
      (AdelicGLn.det K d (rmatUnits b 𝔸[K] x) : 𝔸[K]) • Reduction.ratVec (normCoords b K ξv) := by
  have hv : Reduction.ratVec ξv =
      coords b 𝔸[K] (baseMap (Algebra.ofId K 𝔸[K]) ((coords b K).symm ξv)) := by
    rw [coords_baseMap, LinearEquiv.apply_symm_apply]
    rfl
  funext i
  rw [hv, ← coords_mul]
  simp only [normCoords, LinearEquiv.symm_apply_apply, rmat_mul, det_mul, rmat_baseMap,
    Pi.smul_apply, smul_eq_mul, AdelicGLn.coe_det, rmatUnits_val]
  have e : ((rmat b K ((coords b K).symm ξv)).map (Algebra.ofId K 𝔸[K])).det =
      Algebra.ofId K 𝔸[K] (rmat b K ((coords b K).symm ξv)).det := (AlgHom.map_det _ _).symm
  rw [e, mul_comm]
  rfl

theorem exists_pos_le_height_rmatUnits :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ normOneUnits b, ∀ ξv : Fin d → K, ξv ≠ 0 →
      ε ≤ Reduction.height (rmatUnits b 𝔸[K] x) ξv := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := K) (d := d) (pos_of_basis b) (normPoly b)
    (fun v t y i => by
      rw [aeval_normPoly, aeval_normPoly, normCoords_smul, Fintype.card_fin]
      rfl)
    (fun w t y i => by
      rw [aeval_normPoly, aeval_normPoly, normCoords_smul, Fintype.card_fin]
      rfl)
  have hG : ∀ g ∈ rmatUnits b 𝔸[K] '' (normOneUnits b : Set (𝔸[K] ⊗[K] D)ˣ), ∀ ξv : Fin d → K,
      ξv ≠ 0 → ∃ s : GroundTheory.Global.IdeleGroup K, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) ∧
        ∃ z : Fin 1 → K, z ≠ 0 ∧ (fun y i => MvPolynomial.aeval y (normPoly b i))
          (Reduction.ratVec ξv ᵥ* (g : Matrix (Fin d) (Fin d) 𝔸[K])) =
            (s : 𝔸[K]) • Reduction.ratVec z := by
    rintro _ ⟨x, hx, rfl⟩ ξv hξ
    refine ⟨AdelicGLn.det K d (rmatUnits b 𝔸[K] x), ?_, normCoords b K ξv, ?_, ?_⟩
    · rw [(Reduction.mem_normOneGL).1 hx]
    · intro h0
      have h1 := congrFun h0 0
      simp only [normCoords, Pi.zero_apply] at h1
      refine det_rmat_ne_zero b ?_ h1
      intro h2
      apply hξ
      rw [← LinearEquiv.apply_symm_apply (coords b K) ξv, h2, map_zero]
    · funext i
      simp only [aeval_normPoly]
      rw [rmatUnits_val, normCoords_vecMul]
  obtain ⟨ε, hε, h⟩ := exists_pos_le_height_of_bound
    (rmatUnits b 𝔸[K] '' (normOneUnits b : Set (𝔸[K] ⊗[K] D)ˣ))
    (fun y i => MvPolynomial.aeval y (normPoly b i)) hC (pos_of_basis b) hCb hG
  exact ⟨ε, hε, fun x hx ξv hξ => h _ ⟨x, hx, rfl⟩ ξv hξ⟩

def rationalUnits' : (K ⊗[K] D)ˣ →* (𝔸[K] ⊗[K] D)ˣ :=
  Units.map (baseMap (Algebra.ofId K 𝔸[K]) : K ⊗[K] D →ₐ[K] 𝔸[K] ⊗[K] D).toRingHom.toMonoidHom

theorem exists_isCompact_rmatUnits :
    ∃ C : Set (GL (Fin d) 𝔸[K]), IsCompact C ∧ ∀ x ∈ normOneUnits b,
      ∃ ξ : (K ⊗[K] D)ˣ, rmatUnits b 𝔸[K] ((rationalUnits' ξ)⁻¹ * x) ∈ C := by
  classical
  obtain ⟨ε, hε, hh⟩ := exists_pos_le_height_rmatUnits b
  let L : Fin d → Matrix (Fin d) (Fin d) K := fun j => lmat b K (baseBasis b K j)
  let G : Subgroup (AdelicGLn.AdelicGL K d) :=
    ((rmatUnits b 𝔸[K]).comp (normOneUnits b).subtype).range
  have hG1 : G ≤ Reduction.normOneGL K d := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  have hGL : G ≤ adelicCentralizer L := by
    rintro _ ⟨x, rfl⟩ j
    change _ * (L j).map (Algebra.ofId K 𝔸[K]) = (L j).map (Algebra.ofId K 𝔸[K]) * _
    simp only [L, ← lmat_baseMap, baseMap_baseBasis, MonoidHom.comp_apply, Subgroup.coe_subtype,
      rmatUnits_val]
    exact (lmat_mul_rmat b 𝔸[K] _ _).symm
  obtain ⟨C, hC, hred⟩ := exists_isCompact_centralizer_reduction L G hG1 hGL hε
    (by rintro _ ⟨x, rfl⟩ ξv hξ; exact hh x x.2 ξv hξ)
  refine ⟨C, hC, fun x hx => ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hred _ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨ξ₀, h₀⟩ := exists_rmat_eq b K (γ : Matrix (Fin d) (Fin d) K) fun j => (hγ j).symm
  obtain ⟨ξ₁, h₁⟩ := exists_rmat_eq b K (↑γ⁻¹ : Matrix (Fin d) (Fin d) K) fun j => by
    symm
    calc (↑γ⁻¹ : Matrix (Fin d) (Fin d) K) * L j = ↑γ⁻¹ * (L j * ↑γ) * ↑γ⁻¹ := by
          simp [mul_assoc]
      _ = ↑γ⁻¹ * (↑γ * L j) * ↑γ⁻¹ := by rw [hγ]
      _ = L j * ↑γ⁻¹ := by simp
  have e1 : ξ₀ * ξ₁ = 1 := rmat_injective b K (by rw [rmat_mul, rmat_one, h₀, h₁, γ.mul_inv])
  have e2 : ξ₁ * ξ₀ = 1 := rmat_injective b K (by rw [rmat_mul, rmat_one, h₀, h₁, γ.inv_mul])
  refine ⟨⟨ξ₀, ξ₁, e1, e2⟩, ?_⟩
  have e : rmatUnits b 𝔸[K] (rationalUnits' ⟨ξ₀, ξ₁, e1, e2⟩) = AdelicGLn.diagonal K d γ := by
    ext : 1
    rw [rmatUnits_val]
    show rmat b 𝔸[K] (baseMap (Algebra.ofId K 𝔸[K]) ξ₀) = _
    rw [rmat_baseMap, h₀]
    rfl
  rw [map_mul, map_inv, e]
  exact hγC

end Division

end Anisotropic

end

end GroundTheory.Automorphic
