import Mathlib

namespace KStar.Selmer

open Matrix Module

section Minors

variable {R : Type*} [CommRing R] {m n : Type*}

def minorIdeal (k : ℕ) (A : Matrix m n R) : Ideal R :=
  Ideal.span {x | ∃ (r : Fin k → m) (c : Fin k → n), x = (A.submatrix r c).det}

def fit [Fintype m] (i : ℕ) (Φ : Matrix m n R) : Ideal R :=
  minorIdeal (Fintype.card m - i) Φ

def adjIdeal [Fintype n] [DecidableEq n] (Φ : Matrix n n R) : Ideal R :=
  Ideal.span {x | ∃ i j, x = Φ.adjugate i j}

def fitGen [Fintype m] {M : Type*} [AddCommGroup M] [Module R M] (g : m → M) (i : ℕ) : Ideal R :=
  Ideal.span {x | ∃ (A : Matrix m (Fin (Fintype.card m - i)) R)
    (r : Fin (Fintype.card m - i) → m),
    (∀ j, ∑ a, A a j • g a = 0) ∧ x = (A.submatrix r id).det}

variable (R) in

def modFit (M : Type*) [AddCommGroup M] [Module R M] (i : ℕ) : Ideal R :=
  ⨆ (k : ℕ) (g : Fin k → M) (_ : Submodule.span R (Set.range g) = ⊤), fitGen g i

example (A : Matrix m n R) : minorIdeal 0 A = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨Fin.elim0, Fin.elim0, by simp⟩

end Minors

section Complex

variable {R : Type*} [CommRing R] {m n m' n' : Type*}

def coefMap [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    (n → M) →ₗ[R] (m → M) :=
  LinearMap.pi fun i => ∑ j, Φ i j • LinearMap.proj j

theorem coefMap_apply [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M]
    (v : n → M) (i : m) : coefMap Φ M v i = ∑ j, Φ i j • v j := by
  simp [coefMap, LinearMap.sum_apply]

def H1c [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R (n → M) :=
  LinearMap.ker (coefMap Φ M)

def H1 [Fintype n] (Φ : Matrix m n R) : Submodule R (n → R) :=
  LinearMap.ker Φ.mulVecLin

abbrev H2 [Fintype n] (Φ : Matrix m n R) : Type _ :=
  (m → R) ⧸ LinearMap.range Φ.mulVecLin

theorem coefMap_self [Fintype n] (Φ : Matrix m n R) : coefMap Φ R = Φ.mulVecLin := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [coefMap_apply]
  simp [Matrix.mulVec, dotProduct]

theorem h1c_eq_h1 [Fintype n] (Φ : Matrix m n R) : H1c Φ R = H1 Φ := by
  rw [H1c, H1, coefMap_self]

def IsMinimal (Φ : Matrix m n R) : Prop :=
  ∀ i j, Φ i j ∈ Ideal.jacobson (⊥ : Ideal R)

theorem isMinimal_iff [IsLocalRing R] (Φ : Matrix m n R) :
    IsMinimal Φ ↔ ∀ i j, Φ i j ∈ IsLocalRing.maximalIdeal R := by
  rw [IsMinimal, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

example : IsMinimal (0 : Matrix m n R) := fun _ _ => Ideal.zero_mem _

structure IsQis [Fintype m] [Fintype n] [Fintype n'] (Φ : Matrix m n R) (Φ' : Matrix m' n' R)
    (f₁ : Matrix n' n R) (f₂ : Matrix m' m R) : Prop where
  comm : Φ' * f₁ = f₂ * Φ
  inj₁ : ∀ x, Φ *ᵥ x = 0 → f₁ *ᵥ x = 0 → x = 0
  surj₁ : ∀ x', Φ' *ᵥ x' = 0 → ∃ x, Φ *ᵥ x = 0 ∧ f₁ *ᵥ x = x'
  inj₂ : ∀ y x', f₂ *ᵥ y = Φ' *ᵥ x' → ∃ x, y = Φ *ᵥ x
  surj₂ : ∀ y', ∃ y x', y' = f₂ *ᵥ y + Φ' *ᵥ x'

theorem IsQis.refl [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (Φ : Matrix m n R) :
    IsQis Φ Φ 1 1 where
  comm := by simp
  inj₁ x _ h := by simpa using h
  surj₁ x h := ⟨x, h, by simp⟩
  inj₂ y x h := ⟨x, by simpa using h⟩
  surj₂ y := ⟨y, 0, by simp⟩

def IsHtpyEquiv [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n]
    [DecidableEq m'] [DecidableEq n'] (Φ : Matrix m n R) (Φ' : Matrix m' n' R)
    (f₁ : Matrix n' n R) (f₂ : Matrix m' m R) : Prop :=
  Φ' * f₁ = f₂ * Φ ∧ ∃ (g₁ : Matrix n n' R) (g₂ : Matrix m m' R) (h : Matrix n m R)
    (h' : Matrix n' m' R), Φ * g₁ = g₂ * Φ' ∧ g₁ * f₁ = 1 + h * Φ ∧ g₂ * f₂ = 1 + Φ * h ∧
      f₁ * g₁ = 1 + h' * Φ' ∧ f₂ * g₂ = 1 + Φ' * h'

example [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (Φ : Matrix m n R) :
    IsHtpyEquiv Φ Φ 1 1 :=
  ⟨by simp, 1, 1, 0, 0, by simp, by simp, by simp, by simp, by simp⟩

structure SelfDual [Fintype m] [Fintype n] (ε : R) (Φ : Matrix m n R) where

  J₁₂ : Matrix n m R

  J₂₁ : Matrix m n R

  H : Matrix m m R
  qis : IsQis Φ Φᵀ J₂₁ J₁₂
  symm : J₁₂ - ε • J₂₁ᵀ = Φᵀ * H

def SelfDual.ofSymm [Fintype n] [DecidableEq n] (Φ : Matrix n n R) (h : Φᵀ = Φ) :
    SelfDual 1 Φ where
  J₁₂ := 1
  J₂₁ := 1
  H := 0
  qis := by rw [h]; exact IsQis.refl Φ
  symm := by simp

def SelfDual.ofSkew [Fintype n] [DecidableEq n] (Φ : Matrix n n R) (h : Φᵀ = -Φ) :
    SelfDual (-1) Φ where
  J₁₂ := 1
  J₂₁ := -1
  H := 0
  qis :=
    { comm := by simp [h]
      inj₁ := fun x _ hx => by simpa [Matrix.neg_mulVec] using hx
      surj₁ := fun x hx => ⟨-x, by simpa [h, Matrix.neg_mulVec, Matrix.mulVec_neg] using hx,
        by simp [Matrix.neg_mulVec, Matrix.mulVec_neg]⟩
      inj₂ := fun y x hx => ⟨-x, by simpa [h, Matrix.neg_mulVec, Matrix.mulVec_neg] using hx⟩
      surj₂ := fun y => ⟨y, 0, by simp⟩ }
  symm := by simp

end Complex

section Special

variable {Λ O : Type*} [CommRing Λ] [CommRing O] {m n : Type*}

noncomputable def specLength [Fintype n] (ψ : Λ →+* O) (Φ : Matrix m n Λ) : ℕ∞ :=
  Module.length O (H2 (Φ.map ψ))

abbrev FracMod (O K : Type*) [CommRing O] [Field K] [Algebra O K] : Type _ :=
  K ⧸ (1 : Submodule O K)

end Special

section Koszul

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def koszul₀ (a b : M →ₗ[R] M) : M →ₗ[R] M × M := LinearMap.prod a b

def koszul₁ (a b : M →ₗ[R] M) : M × M →ₗ[R] M := LinearMap.coprod (-b) a

abbrev KoszulH1 (a b : M →ₗ[R] M) : Type _ :=
  LinearMap.ker (koszul₁ a b) ⧸
    (LinearMap.range (koszul₀ a b)).comap (LinearMap.ker (koszul₁ a b)).subtype

abbrev KoszulH2 (a b : M →ₗ[R] M) : Type _ := M ⧸ LinearMap.range (koszul₁ a b)

theorem koszul₁_comp_koszul₀ (a b : M →ₗ[R] M) (h : a ∘ₗ b = b ∘ₗ a) :
    koszul₁ a b ∘ₗ koszul₀ a b = 0 := by
  ext x
  have := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply] at this
  simp [koszul₀, koszul₁, this]

end Koszul

section Lagrangian

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

def IsLagrangian (B : LinearMap.BilinForm k V) (L : Submodule k V) : Prop :=
  B.orthogonal L = L

def IsHalfIsotropic (B : LinearMap.BilinForm k V) (L : Submodule k V) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ 2 * finrank k L = finrank k V

variable {H H' : Type*} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']

def hyperbolic (β : H →ₗ[k] H' →ₗ[k] k) : LinearMap.BilinForm k (H × H') :=
  β.compl₁₂ (LinearMap.fst k H H') (LinearMap.snd k H H') +
    β.flip.compl₁₂ (LinearMap.snd k H H') (LinearMap.fst k H H')

theorem hyperbolic_apply (β : H →ₗ[k] H' →ₗ[k] k) (v w : H × H') :
    hyperbolic β v w = β v.1 w.2 + β w.1 v.2 := by
  simp [hyperbolic]

example : IsHalfIsotropic (hyperbolic (LinearMap.mul k k))
    (LinearMap.range (LinearMap.inl k k k)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    simp [hyperbolic_apply]
  · rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective]
    simp

end Lagrangian

end KStar.Selmer
