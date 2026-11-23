import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

open Formalism.L2.DIV GlobalTheory.FinGL

variable {F : Type} [Field F] {r : ℕ}

abbrev Block (b : Fin r → ℕ) (c : ℕ) : Type := {a : Fin r // b a = c}

def blockMat (b : Fin r → ℕ) (c : ℕ) : Matrix (Block b c) (Block b c) F →* Matrix (Fin r) (Fin r) F where
  toFun g := Matrix.reindex (Equiv.sumCompl fun a => b a = c) (Equiv.sumCompl fun a => b a = c)
    (Matrix.fromBlocks g 0 0 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem blockMat_in (b : Fin r → ℕ) (c : ℕ) (g : Matrix (Block b c) (Block b c) F) (i j : Block b c) :
    blockMat b c g i.1 j.1 = g i j := by
  simp [blockMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) i.2,
    Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) j.2]

theorem blockMat_out (b : Fin r → ℕ) (c : ℕ) (g : Matrix (Block b c) (Block b c) F) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) : blockMat b c g i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · exact absurd ⟨hi, hj⟩ h
  · have : i ≠ j := fun e => hj (e ▸ hi)
    simp [blockMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, this]
  · have : i ≠ j := fun e => hi (e ▸ hj)
    simp [blockMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hj, this]
  · simp [blockMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, Matrix.one_apply]

def toBlock (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) :
    Matrix (Fin d) (Fin d) F →* Matrix (Block b c) (Block b c) F :=
  (Matrix.reindexAlgEquiv F F (monoEquivOfFin (Block b c) h).toEquiv).toMulEquiv.toMonoidHom

def blockEmb (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) :
    GL (Fin d) F →* blockTri (κ := F) b :=
  (Units.map ((blockMat b c).comp (toBlock b c h))).codRestrict (blockTri (κ := F) b) fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show blockMat b c _ i j = 0
    rw [blockMat_out b c _ i j (fun e => by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij; omega)]

theorem blockEmb_in (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) (g : GL (Fin d) F)
    (i j : Fin d) :
    ((blockEmb b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (monoEquivOfFin (Block b c) h i).1
      (monoEquivOfFin (Block b c) h j).1 = (g : Matrix (Fin d) (Fin d) F) i j := by
  show blockMat b c _ _ _ = _
  rw [blockMat_in]
  simp [toBlock]

theorem blockEmb_out (b : Fin r → ℕ) (c : ℕ) {d : ℕ} (h : Fintype.card (Block b c) = d) (g : GL (Fin d) F)
    (i j : Fin r) (hij : ¬ (b i = c ∧ b j = c)) :
    ((blockEmb b c h g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j :=
  blockMat_out b c _ i j hij

variable {V : Type} [AddCommGroup V] [Module ℂ V] {V' : Type} [AddCommGroup V'] [Module ℂ V']

def blockRes (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ) {d : ℕ}
    (h : Fintype.card (Block b c) = d) : Representation ℂ (GL (Fin d) F) V :=
  σ.comp (blockEmb b c h)

def HasFactor (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ) {d : ℕ}
    (h : Fintype.card (Block b c) = d) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin d) F) W) : Prop :=
  ρ.IsIrreducible ∧
    IsIsotypicOfType (MonoidAlgebra ℂ (GL (Fin d) F)) (blockRes b σ c h).asModule ρ.asModule

def SameFactor (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c : ℕ)
    (b' : Fin r → ℕ) (σ' : Representation ℂ (blockTri (κ := F) b') V') (c' : ℕ) : Prop :=
  ∃ (d : ℕ) (h : Fintype.card (Block b c) = d) (h' : Fintype.card (Block b' c') = d)
    (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (ρ : Representation ℂ (GL (Fin d) F) W),
    HasFactor b σ c h ρ ∧ HasFactor b' σ' c' h' ρ

def DistinctFactors (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) : Prop :=
  ∀ c ∈ Set.range b, ∀ c' ∈ Set.range b, c ≠ c' → ¬ SameFactor b σ c b σ c'

def SameFactorSet (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V)
    (b' : Fin r → ℕ) (σ' : Representation ℂ (blockTri (κ := F) b') V') : Prop :=
  (∀ c ∈ Set.range b, ∃ c' ∈ Set.range b', SameFactor b σ c b' σ' c') ∧
    ∀ c' ∈ Set.range b', ∃ c ∈ Set.range b, SameFactor b σ c b' σ' c'

def ProductIrreducible : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b : Fin r → ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ (blockTri (κ := F) b) V),
    IsCuspDatum b σ → DistinctFactors b σ → (parInd b σ).IsIrreducible

def ProductIsoIff : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'),
    IsCuspDatum b σ → DistinctFactors b σ → IsCuspDatum b' σ' → DistinctFactors b' σ' →
      (Nonempty ((parInd b σ).Equiv (parInd b' σ')) ↔ SameFactorSet b σ b' σ')

def CuspidalProduct : Prop := ProductIrreducible ∧ ProductIsoIff

example (σ : Representation ℂ (blockTri (κ := F) (fun _ : Fin r => 0)) V) : DistinctFactors (fun _ => 0) σ := by
  rintro _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ h
  exact absurd rfl h

example (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (c c' : ℕ)
    (h : Fintype.card (Block b c) ≠ Fintype.card (Block b c')) : ¬ SameFactor b σ c b σ c' := by
  rintro ⟨d, h1, h2, -⟩
  exact h (h1.trans h2.symm)

end GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors
