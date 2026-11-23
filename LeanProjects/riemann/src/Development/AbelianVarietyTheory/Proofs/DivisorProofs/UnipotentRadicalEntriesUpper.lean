import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.LeviBlockFrame

theorem blockIndex_val {n i : ℕ} (hi : i + 1 ≤ n) (a : Fin (i + 2)) (k : Fin (blockSizes₂ n i a)) :
    ((blockIndex hi ⟨a, k⟩ : Fin n) : ℕ) = a + k := by
  simp only [blockIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  congr 1
  have : ∀ b : Fin a, blockSizes₂ n i (Fin.castLE a.2.le b) = 1 := fun b => by
    simp only [blockSizes₂, Fin.coe_castLE]; rw [if_pos (by omega)]
  simp [this]

theorem sub_one_ne_zero_imp (R : Type) [CommRing R] (n i : ℕ) (hi : i + 1 ≤ n) (g : GL (Fin n) R)
    (hg : g ∈ GlobalTheory.SmGL.unipRad R (blockIndex hi)) :
    ∀ l j : Fin n, (g.1 - 1) l j ≠ 0 → (l : ℕ) ≤ i ∧ (l : ℕ) < j := by
  intro l j hne
  rw [mem_unipRad] at hg
  obtain ⟨hp, hd⟩ := hg
  obtain ⟨⟨a, x⟩, rfl⟩ := (blockIndex hi).surjective l
  obtain ⟨⟨b, y⟩, rfl⟩ := (blockIndex hi).surjective j
  rw [Matrix.sub_apply] at hne
  rcases lt_trichotomy a b with hab | rfl | hab
  · have ha : (a : ℕ) ≤ i := by have := b.2; omega
    have hx : (x : ℕ) = 0 := by
      have := x.2; simp only [blockSizes₂, if_pos ha] at this; omega
    rw [blockIndex_val, blockIndex_val, hx]
    refine ⟨by omega, ?_⟩
    have : (a : ℕ) < b := hab
    omega
  · exfalso; apply hne
    rw [hd a x y, Matrix.one_apply, Matrix.one_apply]
    simp [(blockIndex hi).injective.eq_iff]
  · exfalso; apply hne
    have h0 := (mem_parab.1 hp) (blockIndex hi ⟨a, x⟩) (blockIndex hi ⟨b, y⟩) (by simpa using hab)
    rw [h0, Matrix.one_apply_ne]
    · simp
    · intro h
      have := congrArg Sigma.fst ((blockIndex hi).injective h)
      exact hab.ne' this

end GlobalTheory.LeviBlockFrame
