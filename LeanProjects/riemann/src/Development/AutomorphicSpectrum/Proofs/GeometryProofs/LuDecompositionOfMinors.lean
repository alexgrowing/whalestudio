import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_lu_of_leading_minors {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (h : ∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧
      (∀ l, V l l = 1) ∧ Y * C = V := by
  classical
  let B : ∀ k : Fin r, Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) F := fun k =>
    Y.submatrix (Fin.castLE k.2) (Fin.castLE k.2)
  have hB : ∀ k, IsUnit (B k).det := fun k => isUnit_iff_ne_zero.2 (h _ k.2)
  let a : ∀ k : Fin r, Fin ((k : ℕ) + 1) → F := fun k =>
    (B k)⁻¹.mulVec (Pi.single (Fin.last _) 1)
  have ha : ∀ k, (B k).mulVec (a k) = Pi.single (Fin.last _) 1 := fun k => by
    simp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB k), Matrix.one_mulVec]
  let C : Matrix (Fin r) (Fin r) F := fun l k =>
    if hlk : (l : ℕ) < (k : ℕ) + 1 then a k ⟨l, hlk⟩ else 0
  have hV : ∀ (k : Fin r) (l : Fin ((k : ℕ) + 1)),
      (Y * C) (Fin.castLE k.2 l) k = (Pi.single (Fin.last (k : ℕ)) (1 : F) :
        Fin ((k : ℕ) + 1) → F) l := by
    intro k l
    rw [← ha k]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    symm
    refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun j _ hj => ?_) (fun b _ => ?_)
    · have hjk : ¬ (j : ℕ) < (k : ℕ) + 1 := fun hlt =>
        hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
      simp only [C, dif_neg hjk, mul_zero]
    · have hb : ((Fin.castLE k.2 b : Fin r) : ℕ) < (k : ℕ) + 1 := b.2
      simp only [C, dif_pos hb]
      rfl
  refine ⟨C, Y * C, fun l k hkl => ?_, fun l k hlk => ?_, fun l => ?_, rfl⟩
  · have hn : ¬ (l : ℕ) < (k : ℕ) + 1 := by
      have : (k : ℕ) < l := hkl
      omega
    simp only [C, dif_neg hn]
  · have hlt : (l : ℕ) < (k : ℕ) + 1 := by
      have : (l : ℕ) < k := hlk
      omega
    have h1 := hV k ⟨l, hlt⟩
    have e : Fin.castLE k.2 (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) = l := by ext; simp
    have hne : (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) ≠ Fin.last (k : ℕ) := by
      intro hh
      have h2 : (l : ℕ) = k := by simpa using Fin.ext_iff.1 hh
      have : (l : ℕ) < k := hlk
      omega
    rw [e, Pi.single_eq_of_ne hne] at h1
    exact h1
  · have h1 := hV l (Fin.last (l : ℕ))
    have e : Fin.castLE l.2 (Fin.last (l : ℕ)) = l := by ext; simp
    rw [e, Pi.single_eq_same] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
