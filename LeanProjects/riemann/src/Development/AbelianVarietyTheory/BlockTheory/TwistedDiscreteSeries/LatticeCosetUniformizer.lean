import Mathlib

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer

open Matrix IsLocalRing

section Objects

variable (O F : Type) [CommRing O] [Field F] [Algebra O F] (n : ℕ)

def integralGL : Subgroup (GL (Fin n) F) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap O F)).range

def inclVec : (Fin n → O) →ₗ[O] (Fin n → F) :=
  (Algebra.linearMap O F).compLeft (Fin n)

def stdLattice : Submodule O (Fin n → F) := LinearMap.range (inclVec O F n)

variable {F n}

def latticeOf (g : GL (Fin n) F) : Submodule O (Fin n → F) :=
  (stdLattice O F n).map
    ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F)).restrictScalars O)

theorem mem_latticeOf (g : GL (Fin n) F) (x : Fin n → F) :
    x ∈ latticeOf O g ↔
      ∃ v : Fin n → O, (g : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i)) = x := by
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

theorem latticeOf_mul_le (g k : GL (Fin n) F) (hk : k ∈ integralGL O F n) :
    latticeOf O (g * k) ≤ latticeOf O g := by
  obtain ⟨k₀, rfl⟩ := hk
  intro x hx
  rw [mem_latticeOf] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  refine ⟨(k₀ : Matrix (Fin n) (Fin n) O) *ᵥ v, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem latticeOf_mul (g k : GL (Fin n) F) (hk : k ∈ integralGL O F n) :
    latticeOf O (g * k) = latticeOf O g := by
  refine le_antisymm (latticeOf_mul_le O g k hk) ?_
  have h := latticeOf_mul_le O (g * k) k⁻¹ (inv_mem hk)
  rwa [mul_inv_cancel_right] at h

def latticeOfCoset (c : GL (Fin n) F ⧸ integralGL O F n) : Submodule O (Fin n → F) :=
  Quotient.liftOn' c (latticeOf O) (by
    intro a b hab
    have h := latticeOf_mul O a (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    rw [mul_inv_cancel_left] at h
    exact h.symm)

@[simp] theorem latticeOfCoset_mk (g : GL (Fin n) F) :
    latticeOfCoset O (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL O F n) = latticeOf O g := rfl

def scaleBy (a : O) (L : Submodule O (Fin n → F)) : Submodule O (Fin n → F) :=
  L.map (a • LinearMap.id)

variable (n) in

def diagUnit (u : Fˣ) (j : ℕ) : GL (Fin n) F where
  val := Matrix.diagonal fun i => if (i : ℕ) < j then (u : F) else 1
  inv := Matrix.diagonal fun i => if (i : ℕ) < j then ((u⁻¹ : Fˣ) : F) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp

def doubleCosetK (t : GL (Fin n) F) : Set (GL (Fin n) F) :=
  {g | ∃ k₁ ∈ integralGL O F n, ∃ k₂ ∈ integralGL O F n, g = k₁ * t * k₂}

def cosetsIn (t : GL (Fin n) F) : Set (GL (Fin n) F ⧸ integralGL O F n) :=
  (fun g => QuotientGroup.mk g) '' doubleCosetK O t

def reduction [IsLocalRing O] (L : Submodule O (Fin n → F)) :
    Submodule (ResidueField O) (Fin n → ResidueField O) where
  carrier := {w | ∃ v : Fin n → O, inclVec O F n v ∈ L ∧ (fun i => residue O (v i)) = w}
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    refine ⟨v + v', by rw [map_add]; exact L.add_mem hv hv', ?_⟩
    funext i
    simp
  zero_mem' := ⟨0, by rw [map_zero]; exact L.zero_mem, by funext i; simp⟩
  smul_mem' := by
    rintro c _ ⟨v, hv, rfl⟩
    obtain ⟨a, rfl⟩ := residue_surjective c
    refine ⟨a • v, by rw [map_smul]; exact L.smul_mem a hv, ?_⟩
    funext i
    simp

end Objects

section Statement

variable (O F : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field F] [Algebra O F] [IsFractionRing O F]

variable {O} in

noncomputable def unifUnit {ϖ : O} (hϖ : Irreducible ϖ) : Fˣ :=
  Units.mk0 (algebraMap O F ϖ) (by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact hϖ.ne_zero)

variable {O} in

noncomputable def tj {ϖ : O} (hϖ : Irreducible ϖ) (n j : ℕ) : GL (Fin n) F :=
  diagUnit n (unifUnit F hϖ) j

variable {O} in

def CosetsAt {ϖ : O} (hϖ : Irreducible ϖ) (n j : ℕ) : Prop :=
  ((∀ g ∈ doubleCosetK O (tj F hϖ n j),
      scaleBy O ϖ (stdLattice O F n) ≤ latticeOf O g ∧ latticeOf O g ≤ stdLattice O F n) ∧
    Set.BijOn (fun c => reduction O (latticeOfCoset O c)) (cosetsIn O (tj F hϖ n j))
      {U : Submodule (ResidueField O) (Fin n → ResidueField O) |
        Module.finrank (ResidueField O) U + j = n}) ∧
  ((∀ g ∈ doubleCosetK O (tj F hϖ n j)⁻¹,
      stdLattice O F n ≤ latticeOf O g ∧ scaleBy O ϖ (latticeOf O g) ≤ stdLattice O F n) ∧
    Set.BijOn (fun c => reduction O (scaleBy O ϖ (latticeOfCoset O c)))
      (cosetsIn O (tj F hϖ n j)⁻¹)
      {U : Submodule (ResidueField O) (Fin n → ResidueField O) |
        Module.finrank (ResidueField O) U = j}) ∧
  (∀ g ∈ doubleCosetK O (tj F hϖ n j), ∃ u : Oˣ,
      (g : Matrix (Fin n) (Fin n) F).det = algebraMap O F (ϖ ^ j * (u : O)))

end Statement

def MinusculeCosets : Prop :=
  ∀ (O F : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [Field F] [Algebra O F] [IsFractionRing O F]
    (ϖ : O) (hϖ : Irreducible ϖ) (n j : ℕ), j ≤ n → CosetsAt F hϖ n j

example {F : Type} [Field F] (n : ℕ) (u : Fˣ) : diagUnit n u 0 = 1 := by
  ext i j
  simp [diagUnit]

example (O F : Type) [CommRing O] [IsLocalRing O] [Field F] [Algebra O F] (n : ℕ) :
    reduction O (latticeOf O (1 : GL (Fin n) F)) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  choose v hv using fun i => residue_surjective (w i)
  refine ⟨v, (mem_latticeOf O 1 _).2 ⟨v, ?_⟩, funext hv⟩
  rw [Units.val_one, Matrix.one_mulVec]
  rfl

example (p : ℕ) [Fact p.Prime] (h : MinusculeCosets) (n j : ℕ) (hj : j ≤ n) :
    CosetsAt ℚ_[p] (PadicInt.irreducible_p (p := p)) n j :=
  haveI : Finite (ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  h ℤ_[p] ℚ_[p] _ _ n j hj

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer
