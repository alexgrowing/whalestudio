import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensL

open MeasureTheory Filter Topology Set Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge

section Reindex

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem reindex_mul' (e : α ≃ β) (A B : Matrix α α ℂ) : reindex e e (A * B) = reindex e e A * reindex e e B := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem reindex_add' (e : α ≃ β) (A B : Matrix α α ℂ) : reindex e e (A + B) = reindex e e A + reindex e e B := by
  ext i j
  simp [Matrix.reindex_apply]

theorem reindex_zero' (e : α ≃ β) : reindex e e (0 : Matrix α α ℂ) = 0 := by
  ext i j
  simp [Matrix.reindex_apply]

theorem exp_reindex (e : α ≃ β) (X : Matrix α α ℂ) :
    NormedSpace.exp (reindex e e X) = reindex e e (NormedSpace.exp X) := by
  letI : NormedRing (Matrix α α ℂ) := Matrix.linftyOpNormedRing
  letI : NormedRing (Matrix β β ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix α α ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℂ (Matrix β β ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix α α ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix β β ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : Continuous (Matrix.reindexAlgEquiv ℂ ℂ e) := by
    show Continuous fun M : Matrix α α ℂ => M.submatrix e.symm e.symm
    exact continuous_id.matrix_submatrix _ _
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hc X).symm

theorem l1_entry_sum_reindex (e : α ≃ β) (X : Matrix α α ℂ) :
    ∑ i, ∑ j, ‖reindex e e X i j‖ = ∑ i, ∑ j, ‖X i j‖ := by
  calc ∑ i, ∑ j, ‖reindex e e X i j‖ = ∑ i, ∑ j, ‖X (e.symm i) (e.symm j)‖ := rfl
    _ = ∑ i, ∑ j, ‖X i (e.symm j)‖ := e.symm.sum_comp (fun i => ∑ j, ‖X i (e.symm j)‖)
    _ = ∑ i, ∑ j, ‖X i j‖ := Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => ‖X i j‖)

end Reindex

variable {n P Q : ℕ}

theorem reindex_Jpq (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
    (h2 : ∀ j, ε (e (Sum.inr j)) = false) : reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨s, rfl⟩ := e.surjective i
  obtain ⟨t, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.UG.Jpq,
    Formalism.REAL.Jm, Matrix.diagonal_apply, e.injective.eq_iff]
  rcases s with s | s <;> rcases t with t | t <;>
    simp [h1, h2, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem lieU_iff (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
    (h2 : ∀ j, ε (e (Sum.inr j)) = false) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ Formalism.BasicNotions.lieU P Q ↔ Formalism.REAL.inG ε (reindex e e X) := by
  have hJ := reindex_Jpq ε e h1 h2
  show Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔
    (reindex e e X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * reindex e e X = 0
  have hc : (reindex e e X)ᴴ = reindex e e Xᴴ := by
    simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [← hJ, hc, ← reindex_mul', ← reindex_mul', ← reindex_add', ← reindex_zero' e]
  exact (Matrix.reindex e e).injective.eq_iff.symm

theorem upqIn (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : UpqIn ε e := by
  unfold UpqIn
  intro h1 h2 g
  have hJ := reindex_Jpq ε e h1 h2
  let g' : Formalism.UG.Upq P Q := g
  have hct : ∀ M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  have hg : g.matᴴ * Formalism.UG.Jpq P Q * g.mat = Formalism.UG.Jpq P Q := by
    have h : Formalism.UG.cT (starRingEnd ℂ) g.mat * Formalism.UG.Jpq P Q * g.mat = Formalism.UG.Jpq P Q := g'.2
    rwa [hct] at h
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.map (Matrix.reindexAlgEquiv ℂ ℂ e : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →* Matrix (Fin n) (Fin n) ℂ) g'.1
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) = reindex e e g.mat := rfl
  have hmem : u ∈ Formalism.REAL.UJ ε := by
    show (u : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * (u : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm ε
    have hc : (reindex e e g.mat)ᴴ = reindex e e g.matᴴ := by
      simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    rw [hu, ← hJ, hc, ← reindex_mul', ← reindex_mul', hg]
  exact ⟨⟨u, hmem⟩, hu⟩

theorem setEq (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : SetEq ε e := by
  intro h1 h2 r
  ext g
  constructor
  · rintro ⟨a, ⟨t, ht, rfl⟩, hat⟩
    have hexp : umat (expC ε t) = NormedSpace.exp (linT ε t) := uMat_expC' ε t
    have hY : Formalism.REAL.inG ε (linT ε t) := by rw [linT_apply]; exact inG_of_gLie ε _
    have hXY : reindex e e ((reindex e e).symm (linT ε t)) = linT ε t := (reindex e e).apply_symm_apply _
    have hX : (reindex e e).symm (linT ε t) ∈ Formalism.BasicNotions.lieU P Q := (lieU_iff ε e h1 h2 _).2 (by rw [hXY]; exact hY)
    refine ⟨⟨_, hX⟩, ?_, ?_⟩
    · show ∑ i, ∑ j, ‖(reindex e e).symm (linT ε t) i j‖ < r
      rw [← l1_entry_sum_reindex e, hXY]; exact ht
    · apply (reindex e e).injective
      show reindex e e (Formalism.BasicNotions.UpqT.mat g) = reindex e e (NormedSpace.exp ((reindex e e).symm (linT ε t)))
      rw [← hat, hexp, ← exp_reindex, hXY]
  · rintro ⟨X, hXb, hgX⟩
    have hY : Formalism.REAL.inG ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) :=
      (lieU_iff ε e h1 h2 _).1 X.2
    refine ⟨expC ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))), ⟨_, ?_, rfl⟩, ?_⟩
    · show ∑ i, ∑ j, ‖linT ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) i j‖ < r
      rw [linT_cM hY, l1_entry_sum_reindex]; exact hXb
    · have hexp : umat (expC ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) =
          NormedSpace.exp (linT ε (cM ε (reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))) :=
        uMat_expC' ε _
      rw [hexp, linT_cM hY, hgX, exp_reindex]

end Formalism.MainNotions.S.Gauge
