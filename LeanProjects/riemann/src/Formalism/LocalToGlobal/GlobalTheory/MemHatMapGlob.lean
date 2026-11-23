import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def mapQ (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) : Submodule (𝓞 E) (m → E) :=
  Λ.map ((Matrix.mulVecLin Q).restrictScalars (𝓞 E))

theorem mem_mapQ (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) (y : m → E) :
    y ∈ mapQ Q Λ ↔ ∃ x ∈ Λ, Q *ᵥ x = y := Iff.rfl

theorem mapQ_mapQ (Q : Matrix m n E) (Q' : Matrix n m E) (h : Q' * Q = 1) (Λ : Submodule (𝓞 E) (n → E)) :
    mapQ Q' (mapQ Q Λ) = Λ := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    show Q' *ᵥ (Q *ᵥ z) ∈ Λ
    rwa [mulVec_mulVec, h, one_mulVec]
  · intro hx
    exact ⟨Q *ᵥ x, ⟨x, hx, rfl⟩, by
      show Q' *ᵥ (Q *ᵥ x) = x
      rw [mulVec_mulVec, h, one_mulVec]⟩

theorem hat_map_le (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜) (hu : u ∈ hat F Λ) :
    (Q.map ιA) *ᵥ u ∈ hat F (mapQ Q Λ) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨Q *ᵥ y, ⟨y, hy, rfl⟩, ?_⟩
    funext i
    exact RingHom.map_mulVec ιA Q y i
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ s hu

theorem map_mul_map (Q : Matrix m n E) (Q' : Matrix n m E) (h : Q * Q' = 1) :
    Q.map ιA * Q'.map ιA = (1 : Matrix m m 𝒜) := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_hat_map (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    (Λ : Submodule (𝓞 E) (n → E)) (v : m → 𝒜) : v ∈ hat F (mapQ Q Λ) ↔ (Q'.map ιA) *ᵥ v ∈ hat F Λ := by
  constructor
  · intro hv
    have := hat_map_le (F := F) Q' (mapQ Q Λ) v hv
    rwa [mapQ_mapQ Q Q' h2] at this
  · intro hv
    have := hat_map_le (F := F) Q Λ _ hv
    rwa [mulVec_mulVec, map_mul_map Q Q' h1, one_mulVec] at this

def conjQ (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1) (g : GL n 𝒜) : GL m 𝒜 where
  val := Q.map ιA * (g : Matrix n n 𝒜) * Q'.map ιA
  inv := Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA
  val_inv := by
    have e : Q'.map ιA * Q.map ιA = (1 : Matrix n n 𝒜) := map_mul_map Q' Q h2
    calc Q.map ιA * (g : Matrix n n 𝒜) * Q'.map ιA * (Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA)
        = Q.map ιA * ((g : Matrix n n 𝒜) * (Q'.map ιA * Q.map ιA) * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜)) * Q'.map ιA := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [e, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, map_mul_map Q Q' h1]
  inv_val := by
    have e : Q'.map ιA * Q.map ιA = (1 : Matrix n n 𝒜) := map_mul_map Q' Q h2
    calc Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA * (Q.map ιA * (g : Matrix n n 𝒜) * Q'.map ιA)
        = Q.map ιA * (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * (Q'.map ιA * Q.map ιA) * (g : Matrix n n 𝒜)) * Q'.map ιA := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [e, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, map_mul_map Q Q' h1]

theorem det_conjQ (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1) (g : GL n 𝒜) :
    ((conjQ Q Q' h1 h2 g : GL m 𝒜) : Matrix m m 𝒜).det = (g : Matrix n n 𝒜).det :=
  Matrix.det_conj_of_mul_eq_one (map_mul_map Q Q' h1) (map_mul_map Q' Q h2)

theorem mem_hat_map_glob (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (g : GL n 𝒜) (v : m → 𝒜) :
    v ∈ hat F (mapQ Q (globLat g Λ)) ↔
      (((conjQ Q Q' h1 h2 g)⁻¹ : GL m 𝒜) : Matrix m m 𝒜) *ᵥ v ∈ hat F (mapQ Q Λ) := by
  rw [mem_hat_map Q Q' h1 h2, mem_hat_glob hΛ, mem_hat_map Q Q' h1 h2]
  have e : Q'.map ιA * Q.map ιA = (1 : Matrix n n 𝒜) := map_mul_map Q' Q h2
  have : (Q'.map ιA) *ᵥ ((((conjQ Q Q' h1 h2 g)⁻¹ : GL m 𝒜) : Matrix m m 𝒜) *ᵥ v) =
      ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ ((Q'.map ιA) *ᵥ v) := by
    show (Q'.map ιA) *ᵥ ((Q.map ιA * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * Q'.map ιA) *ᵥ v) = _
    rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]
  rw [this]

end Formalism.L2.GlobalTheoryTheory.Comp

end
