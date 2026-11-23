import Formalism.LocalToGlobal.GlobalTheory.MemHatMapGlob

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem glob_companion (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) {a : 𝓞 E} (ha : a ≠ 0) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    globLat g (Λ ⊔ Ideal.span {a} • dl σ J Λ) = globLat g Λ ⊔ Ideal.span {a} • dl σ J (globLat g Λ) := by
  rw [glob_sup hΛ (isLat_smul (hJ _ hΛ) ha), glob_smul (hJ _ hΛ) ha, glob_dl σ J hJ hΛ g hg]

theorem glob_selfdual (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (hsd : dl σ J Λ = Λ) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) : dl σ J (globLat g Λ) = globLat g Λ := by
  rw [← glob_dl σ J hJ hΛ g hg, hsd]

theorem hform_mulVec_rect {A : Type} [CommRing A] (τ : A →+* A) (J' : Matrix m m A) (Q : Matrix m n A)
    (x y : n → A) : hform τ J' (Q *ᵥ x) (Q *ᵥ y) = hform τ (cT τ Q * J' * Q) x y := by
  have H : ∀ {p : Type} [Fintype p] (M : Matrix p p A) (a b : p → A),
      ∑ i, ∑ j, a i * M i j * b j = (a ᵥ* M) ⬝ᵥ b := by
    intro p _ M a b
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  unfold Formalism.UG.hform Formalism.UG.cT
  rw [show (∑ i, ∑ j, τ ((Q *ᵥ x) i) * J' i j * (Q *ᵥ y) j)
      = ((fun i => τ ((Q *ᵥ x) i)) ᵥ* J') ⬝ᵥ (Q *ᵥ y) from H _ _ _,
    show (∑ i, ∑ j, τ (x i) * ((Q.map τ)ᵀ * J' * Q) i j * y j)
      = ((fun i => τ (x i)) ᵥ* ((Q.map τ)ᵀ * J' * Q)) ⬝ᵥ y from H _ _ _]
  have hx : (fun i => τ ((Q *ᵥ x) i)) = (fun i => τ (x i)) ᵥ* (Q.map τ)ᵀ := by
    rw [Matrix.vecMul_transpose]
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hx, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem dl_mapQ (σ : E →ₐ[F] E) (J : Matrix n n E) (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1)
    (hQ : cT (σ : E →+* E) Q * (1 : Matrix m m E) * Q = J) (M : Submodule (𝓞 E) (n → E)) :
    dl σ (1 : Matrix m m E) (mapQ Q M) = mapQ Q (dl σ J M) := by
  have key : ∀ a b, hform (σ : E →+* E) (1 : Matrix m m E) (Q *ᵥ a) (Q *ᵥ b) = hform (σ : E →+* E) J a b := by
    intro a b
    rw [hform_mulVec_rect, hQ]
  unfold dl mapQ
  rw [Submodule.map_span]
  congr 1
  ext x
  unfold dualSet
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨Q' *ᵥ x, ?_, ?_⟩
    · intro y hy
      have h := hx (Q *ᵥ y) ⟨y, hy, rfl⟩
      rw [← key y (Q' *ᵥ x), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      exact h
    · show Q *ᵥ (Q' *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rintro ⟨z, hz, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    show hform _ 1 (Q *ᵥ y) (Q *ᵥ z) ∈ _
    rw [key]
    exact hz y hy

theorem cT_map (σ : E →ₐ[F] E) {p q : Type} (Q : Matrix p q E) :
    cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) = (cT (σ : E →+* E) Q).map ιA := by
  unfold Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  first
  | rfl
  | simp [Formalism.UG.sigR, Formalism.UG.inclE]
  | simp [Formalism.UG.P.sigR, Formalism.UG.P.inclE]
  | simp [Formalism.UG.CS.sigR, Formalism.UG.CS.inclE]
  | (unfold Formalism.UG.sigR; done)

theorem conjQ_mem (σ : E →ₐ[F] E) (J : Matrix n n E) (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) (hQ : cT (σ : E →+* E) Q * (1 : Matrix m m E) * Q = J) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    conjQ Q Q' h1 h2 g ∈ UPts σ (1 : Matrix m m E) (FiniteAdeleRing (𝓞 F) F) := by
  have hcTA : ∀ {p q r : Type} [Fintype q] (M : Matrix p q (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
      (N : Matrix q r (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (M * N) =
        cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) N * cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) M := by
    intro p q r _ M N
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hcTE : ∀ {p q r : Type} [Fintype q] (M : Matrix p q E) (N : Matrix q r E),
      cT (σ : E →+* E) (M * N) = cT (σ : E →+* E) N * cT (σ : E →+* E) M := by
    intro p q r _ M N
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hcT1 : cT (σ : E →+* E) (1 : Matrix m m E) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hmap1 : (1 : Matrix m m E).map ιA = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hA : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) * Q.map ιA = J.map ιA := by
    rw [cT_map, ← Matrix.map_mul, ← hQ, Matrix.mul_one]
  have hE : cT (σ : E →+* E) Q' * J * Q' = 1 := by
    rw [← hQ, Matrix.mul_one, ← Matrix.mul_assoc, ← hcTE, Matrix.mul_assoc, h1, hcT1, Matrix.mul_one]
  have hA' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) * J.map ιA * Q'.map ιA = 1 := by
    rw [cT_map, ← Matrix.map_mul, ← Matrix.map_mul, hE]
    exact hmap1
  have hg' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * J.map ιA *
      (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = J.map ιA := hg
  show cT (sigR σ (FiniteAdeleRing (𝓞 F) F))
      (Q.map ιA * (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * Q'.map ιA) * (1 : Matrix m m E).map ιA *
      (Q.map ιA * (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * Q'.map ιA) = (1 : Matrix m m E).map ιA
  rw [hmap1, Matrix.mul_one, hcTA, hcTA]
  calc cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) *
        (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
          cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA)) *
        (Q.map ιA * (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) * Q'.map ιA)
      = cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) *
          (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *
            (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) * Q.map ιA) *
            (g : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) * Q'.map ιA := by
        simp only [Matrix.mul_assoc]
    _ = cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q'.map ιA) * J.map ιA * Q'.map ιA := by rw [hA, hg']
    _ = 1 := hA'

theorem exists_unitary_one_det_eq (σ : E →ₐ[F] E) (G : GL m 𝒜) (hG : G ∈ UPts σ (1 : Matrix m m E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ x : GL (Fin 1) 𝒜, x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det x = Matrix.GeneralLinearGroup.det G := by
  have hmap1 : ∀ {p : Type} [Fintype p] [DecidableEq p], (1 : Matrix p p E).map ιA = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hG' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (G : Matrix m m 𝒜) * (1 : Matrix m m E).map ιA *
      (G : Matrix m m 𝒜) = (1 : Matrix m m E).map ιA := hG
  rw [hmap1, Matrix.mul_one] at hG'
  set u : 𝒜ˣ := Matrix.GeneralLinearGroup.det G with hu
  have hud : (u : 𝒜) = Matrix.det (G : Matrix m m 𝒜) := Matrix.GeneralLinearGroup.val_det_apply G
  have hd : sigR σ (FiniteAdeleRing (𝓞 F) F) (u : 𝒜) * (u : 𝒜) = 1 := by
    have h := congrArg Matrix.det hG'
    rw [Matrix.det_mul, Matrix.det_one] at h
    unfold Formalism.UG.cT at h
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    rw [hud]
    exact h
  let x : GL (Fin 1) 𝒜 :=
    ⟨Matrix.diagonal (fun _ => (u : 𝒜)), Matrix.diagonal (fun _ => ((u⁻¹ : 𝒜ˣ) : 𝒜)),
      by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
  refine ⟨x, ?_, ?_⟩
  · show cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Matrix.diagonal (fun _ : Fin 1 => (u : 𝒜))) *
        (1 : Matrix (Fin 1) (Fin 1) E).map ιA * Matrix.diagonal (fun _ : Fin 1 => (u : 𝒜)) =
        (1 : Matrix (Fin 1) (Fin 1) E).map ιA
    rw [hmap1, Matrix.mul_one]
    unfold Formalism.UG.cT
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hd
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show Matrix.det (Matrix.diagonal (fun _ : Fin 1 => (u : 𝒜))) = (u : 𝒜)
    rw [Matrix.det_diagonal]
    simp

end Formalism.L2.GlobalTheoryTheory.Comp

end
