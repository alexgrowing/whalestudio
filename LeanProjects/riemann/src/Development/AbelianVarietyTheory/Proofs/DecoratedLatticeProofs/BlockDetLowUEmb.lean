import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.LowerHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def lowU (ν : Matrix D A k) : GL (A ⊕ D) k where
  val := fromBlocks 1 0 ν 1
  inv := fromBlocks 1 0 (-ν) 1
  val_inv := by rw [fromBlocks_multiply]; simp
  inv_val := by rw [fromBlocks_multiply]; simp

theorem val_lowU (ν : Matrix D A k) : (lowU ν).1 = fromBlocks 1 0 ν 1 := rfl

open Classical in

def blockDet (j : GL (A ⊕ D) k) : kˣ :=
  if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1

theorem val_emb_one (m : GL D k) :
    (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1 = fromBlocks 1 0 0 m.1 := by
  rw [val_emb₂]; simp

theorem blockDet_lowU_emb (ν : Matrix D A k) (m : GL D k) :
    blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) = GeneralLinearGroup.det m := by
  have h : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1.toBlocks₂₂ = m.1 := by
    rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
  have h0 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1.toBlocks₂₂.det ≠ 0 := by
    rw [h]; exact (GeneralLinearGroup.det m).ne_zero
  rw [blockDet, dif_pos h0]; ext; rw [Units.val_mk0, h, GeneralLinearGroup.val_det_apply]

theorem emb_mul_lowU (m : GL D k) (ν : Matrix D A k) :
    emb₂ k (Equiv.refl (A ⊕ D)) (1, m) * lowU ν = lowU (m.1 * ν) * emb₂ k (Equiv.refl (A ⊕ D)) (1, m) := by
  ext1
  rw [Units.val_mul, Units.val_mul, val_emb_one, val_lowU, val_lowU, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem emb_mul_emb (m m' : GL D k) :
    emb₂ k (Equiv.refl (A ⊕ D)) (1, m) * emb₂ k (Equiv.refl (A ⊕ D)) (1, m') =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, m * m') := by
  rw [← map_mul]; simp

theorem mtor_eq (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ e : GL (A ⊕ D) k) = emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e) := by
  ext1
  rw [val_emb_one, mtor, val_torusElt, val_torusElt]
  ext (i | i) (j | j) <;> simp [diagonal_apply, Matrix.one_apply]

theorem inv_lowU (ν : Matrix D A k) : (lowU ν)⁻¹ = lowU (-ν) := Units.ext rfl

theorem lowU_mem {ν : Matrix D A k} (h : ∀ i a, valuation k (ν i a) < 1) : lowU ν ∈ parahoric k A D := by
  rw [mem_parahoric, GlobalTheory.StepData.mem_KO]
  refine ⟨⟨?_, ?_⟩, fun i j => by simpa [val_lowU] using h i j⟩
  · rintro (i | i) (j | j) <;> simp only [val_lowU, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact (h i j).le
    · split_ifs <;> simp
  · rw [inv_lowU]
    rintro (i | i) (j | j) <;> simp only [val_lowU, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact neg_mem (h i j).le
    · split_ifs <;> simp

theorem emb_mem {κ : GL D k} (h : κ ∈ KO k D) : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ parahoric k A D := by
  rw [mem_parahoric, GlobalTheory.StepData.mem_KO]
  obtain ⟨h1, h2⟩ := GlobalTheory.StepData.mem_KO.1 h
  have hinv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ))⁻¹ = emb₂ k (Equiv.refl (A ⊕ D)) (1, κ⁻¹) := by
    rw [← map_inv]; simp
  refine ⟨⟨?_, ?_⟩, fun i j => by simp [val_emb_one]⟩
  · rintro (i | i) (j | j) <;> simp only [val_emb_one, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact zero_mem _
    · exact h1 i j
  · rw [hinv]
    rintro (i | i) (j | j) <;> simp only [val_emb_one, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact zero_mem _
    · exact h2 i j

variable (k D) in

def mLat : AddSubgroup (D → k) where
  carrier := {v | ∀ i, valuation k (v i) < 1}
  add_mem' ha hb i := by simpa using Valuation.map_add_lt _ (ha i) (hb i)
  zero_mem' i := by simp
  neg_mem' ha i := by simpa using ha i

def preLat (m : Matrix D D k) : AddSubgroup (D → k) := (mLat k D).comap (Matrix.mulVecLin m).toAddMonoidHom

theorem mem_mLat {v : D → k} : v ∈ mLat k D ↔ ∀ i, valuation k (v i) < 1 := Iff.rfl

theorem mem_preLat {m : Matrix D D k} {v : D → k} : v ∈ preLat m ↔ m.mulVec v ∈ mLat k D := Iff.rfl

end GlobalTheory.LowerHecke

end
