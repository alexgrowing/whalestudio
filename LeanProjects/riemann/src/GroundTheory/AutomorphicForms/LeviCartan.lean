import Mathlib
import GroundTheory.AutomorphicForms.AdmissibleInduction
import GroundTheory.AutomorphicForms.Cartan

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel

section Smith

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_eq_mul_diagonal_pow_mul_fintype {ϖ : R} (hϖ : Irreducible ϖ)
    (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    ∃ (P Q : GL ι R) (e : ι → ℕ),
      A = (P : Matrix ι ι R) * diagonal (fun i => ϖ ^ e i) * (Q : Matrix ι ι R) := by
  let eq := Fintype.equivFin ι
  obtain ⟨P, Q, e, -, h⟩ := Cartan.exists_eq_mul_diagonal_pow_mul hϖ (reindex eq eq A)
    (by rwa [det_reindex_self])
  let φ := reindexAlgEquiv R R eq.symm
  refine ⟨Units.map φ.toMonoidHom P, Units.map φ.toMonoidHom Q, e ∘ eq, ?_⟩
  have h1 : φ (reindex eq eq A) = A := by
    ext i j
    simp [φ, reindexAlgEquiv_apply]
  have h2 : φ (diagonal fun i => ϖ ^ e i) = diagonal fun i => ϖ ^ (e ∘ eq) i := by
    rw [reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, submatrix_diagonal_equiv]
    rfl
  rw [← h1, h, map_mul, map_mul, h2]
  rfl

end Smith

section Blocks

variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)

abbrev blockOf : Fin n → Set.range β := Set.rangeFactorization β

abbrev Fiber (a : Set.range β) : Type := {i : Fin n // blockOf β i = a}

variable (R : Type*) [CommRing R]

def blockAssemble : (∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R) →+* Matrix (Fin n) (Fin n) R :=
  (reindexAlgEquiv R R (Equiv.sigmaFiberEquiv (blockOf β))).toRingEquiv.toRingHom.comp
    (blockDiagonal'RingHom (Fiber β) R)

def blocks (X : Matrix (Fin n) (Fin n) R) (a : Set.range β) : Matrix (Fiber β a) (Fiber β a) R :=
  fun i j => X i j

variable {β R}

theorem sigmaFiberEquiv_symm_eq {i : Fin n} {a : Set.range β} (hi : blockOf β i = a) :
    (Equiv.sigmaFiberEquiv (blockOf β)).symm i = ⟨a, ⟨i, hi⟩⟩ := by
  subst hi
  rfl

theorem blockAssemble_apply (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    (i j : Fin n) :
    blockAssemble β R X i j = blockDiagonal' X ((Equiv.sigmaFiberEquiv (blockOf β)).symm i)
      ((Equiv.sigmaFiberEquiv (blockOf β)).symm j) := rfl

theorem blockAssemble_apply_of_eq (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    {i j : Fin n} {a : Set.range β} (hi : blockOf β i = a) (hj : blockOf β j = a) :
    blockAssemble β R X i j = X a ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [blockAssemble_apply, sigmaFiberEquiv_symm_eq hi, sigmaFiberEquiv_symm_eq hj,
    blockDiagonal'_apply_eq]

theorem blockAssemble_apply_of_ne (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    {i j : Fin n} (h : β i ≠ β j) : blockAssemble β R X i j = 0 := by
  rw [blockAssemble_apply, sigmaFiberEquiv_symm_eq rfl, sigmaFiberEquiv_symm_eq rfl]
  exact blockDiagonal'_apply_ne _ _ _ fun e => h (congrArg Subtype.val e)

theorem blocks_blockAssemble (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R) :
    blocks β R (blockAssemble β R X) = X := by
  funext a
  ext i j
  exact blockAssemble_apply_of_eq X i.2 j.2

theorem blockAssemble_blocks {X : Matrix (Fin n) (Fin n) R}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) : blockAssemble β R (blocks β R X) = X := by
  ext i j
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    rw [blockAssemble_apply_of_eq _ rfl hj]
    rfl
  · rw [blockAssemble_apply_of_ne _ h, hX i j h]

theorem blockAssemble_diagonal (d : ∀ a : Set.range β, Fiber β a → R) :
    blockAssemble β R (fun a => diagonal (d a)) =
      diagonal fun i => d (blockOf β i) ⟨i, rfl⟩ := by
  ext i j
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    rw [blockAssemble_apply_of_eq _ rfl hj]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ (fun e => hij (congrArg Subtype.val e)), diagonal_apply_ne _ hij]
  · have hij : i ≠ j := fun e => h (by rw [e])
    rw [blockAssemble_apply_of_ne _ h, diagonal_apply_ne _ hij]

theorem blocks_mul {X Y : Matrix (Fin n) (Fin n) R} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (hY : ∀ i j, β i ≠ β j → Y i j = 0) :
    blocks β R (X * Y) = blocks β R X * blocks β R Y := by
  conv_lhs => rw [← blockAssemble_blocks hX, ← blockAssemble_blocks hY, ← map_mul]
  rw [blocks_blockAssemble]

end Blocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem exists_eq_mul_diagPow_mul_levi {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    ∃ μ : Fin n → ℤ, ∃ k₁ ∈ levi F n β ⊓ integralGL F n, ∃ k₂ ∈ levi F n β ⊓ integralGL F n,
      m = k₁ * Cartan.diagPow F n μ * k₂ := by
  classical
  have hϖ := Cartan.uniformizer_ne_zero F
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n (isCompact_singleton (x := m))
  have ht' : ∀ i j, (uniformizer F : F) ^ t * m i j ∈ 𝒪[F] := ht m rfl
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, ht' i j⟩
  have hAmap : A.map (𝒪[F]).subtype = (uniformizer F : F) ^ t • (m : Matrix (Fin n) (Fin n) F) := by
    ext i j
    rfl
  have hm0 : ∀ i j, β i ≠ β j → (m : Matrix (Fin n) (Fin n) F) i j = 0 := mem_levi.1 hm
  have hminv0 : ∀ i j, β i ≠ β j → ((m⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 :=
    mem_levi.1 ((levi F n β).inv_mem hm)
  have hA0 : ∀ i j, β i ≠ β j → A i j = 0 := by
    intro i j h
    apply Subtype.ext
    show (uniformizer F : F) ^ t * m i j = 0
    rw [hm0 i j h, mul_zero]

  have hblk : blocks β F (m : Matrix (Fin n) (Fin n) F) *
      blocks β F ((m⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← blocks_mul hm0 hminv0, Units.mul_inv]
    funext a
    ext i j
    show (1 : Matrix (Fin n) (Fin n) F) i.1 j.1 = (1 : Matrix (Fiber β a) (Fiber β a) F) i j
    by_cases hij : i = j
    · rw [hij, one_apply_eq, one_apply_eq]
    · rw [one_apply_ne hij, one_apply_ne (fun e => hij (Subtype.ext e))]
  have hdet : ∀ a, (blocks β 𝒪[F] A a).det ≠ 0 := by
    intro a h
    have h1 := congrArg (𝒪[F]).subtype h
    rw [map_zero, RingHom.map_det] at h1
    have h2 : (RingHom.mapMatrix (𝒪[F]).subtype) (blocks β 𝒪[F] A a) =
        (uniformizer F : F) ^ t • blocks β F (m : Matrix (Fin n) (Fin n) F) a := by
      ext i j
      rfl
    rw [h2, det_smul] at h1
    have h3 : (blocks β F (m : Matrix (Fin n) (Fin n) F) a) *
        (blocks β F ((m⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a) = 1 :=
      congrFun hblk a
    have h4 := congrArg Matrix.det h3
    rw [det_mul, det_one] at h4
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hϖ)) (left_ne_zero_of_mul_eq_one h4) h1
  choose P Q e hPQ using fun a => exists_eq_mul_diagonal_pow_mul_fintype
    (irreducible_uniformizer F) (blocks β 𝒪[F] A a) (hdet a)
  let Ψ := blockAssemble β 𝒪[F]
  let PU : GL (Fin n) 𝒪[F] := Units.map Ψ.toMonoidHom (MulEquiv.piUnits.symm P)
  let QU : GL (Fin n) 𝒪[F] := Units.map Ψ.toMonoidHom (MulEquiv.piUnits.symm Q)
  let e' : Fin n → ℕ := fun i => e (blockOf β i) ⟨i, rfl⟩
  have hAeq : A = (PU : Matrix (Fin n) (Fin n) 𝒪[F]) *
      diagonal (fun i => (GLnLocal.uniformizer F) ^ e' i) * (QU : Matrix (Fin n) (Fin n) 𝒪[F]) := by
    have hb : blocks β 𝒪[F] A = (fun a => (P a : Matrix _ _ 𝒪[F])) *
        (fun a => diagonal fun i => (GLnLocal.uniformizer F) ^ e a i) * (fun a => (Q a : Matrix _ _ 𝒪[F])) := by
      funext a
      exact hPQ a
    have hPU : (PU : Matrix (Fin n) (Fin n) 𝒪[F]) = Ψ (fun a => (P a : Matrix _ _ 𝒪[F])) := rfl
    have hQU : (QU : Matrix (Fin n) (Fin n) 𝒪[F]) = Ψ (fun a => (Q a : Matrix _ _ 𝒪[F])) := rfl
    rw [hPU, hQU, ← blockAssemble_blocks hA0, hb, map_mul, map_mul, blockAssemble_diagonal]
  have hlevi : ∀ U : GL (Fin n) 𝒪[F], (∀ i j, β i ≠ β j → (U : Matrix (Fin n) (Fin n) 𝒪[F]) i j = 0) →
      integralGLHom F n U ∈ levi F n β ⊓ integralGL F n := by
    intro U hU
    refine ⟨mem_levi.2 fun i j h => ?_, ⟨U, rfl⟩⟩
    rw [integralGLHom_apply, hU i j h]
    rfl
  refine ⟨fun i => (e' i : ℤ) - t, integralGLHom F n PU,
    hlevi PU fun i j h => blockAssemble_apply_of_ne _ h, integralGLHom F n QU,
    hlevi QU fun i j h => blockAssemble_apply_of_ne _ h, ?_⟩
  have key := congrArg (RingHom.mapMatrix (𝒪[F]).subtype) hAeq
  simp only [map_mul, RingHom.mapMatrix_apply] at key
  rw [hAmap, diagonal_map (map_zero _)] at key
  have hdiag : (diagonal fun i => ((𝒪[F]).subtype (GLnLocal.uniformizer F ^ e' i))) =
      (uniformizer F : F) ^ t • diagonal fun i => (uniformizer F : F) ^ ((e' i : ℤ) - t) := by
    ext i j
    rw [Matrix.smul_apply, diagonal_apply, diagonal_apply]
    split_ifs
    · rw [smul_eq_mul, map_pow, zpow_sub₀ hϖ, zpow_natCast, zpow_natCast,
        mul_div_cancel₀ _ (pow_ne_zero _ hϖ)]
      rfl
    · rw [smul_zero]
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul] at key
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Cartan.coe_diagPow]
  exact smul_right_injective _ (pow_ne_zero t hϖ) key

end Parabolic

end GroundTheory.Automorphic
