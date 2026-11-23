import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

private theorem UpperTheory.Reformulated.B.G5.irr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ}
    {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R} (P Q : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) (H : ∀ g ∈ U, a g = Q * a' g * P)
    (hirr : ∀ S : Submodule R (Fin m → R),
      (∀ g ∈ U, ∀ v ∈ S, (a g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤)
    (S : Submodule R (Fin m → R)) (hS : ∀ g ∈ U, ∀ v ∈ S, (a' g).mulVec v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have key : ∀ v : Fin m → R, P.mulVec (Q.mulVec v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  have mem : ∀ v : Fin m → R, v ∈ S.comap P.mulVecLin ↔ P.mulVec v ∈ S := fun v => Iff.rfl
  have hst : ∀ g ∈ U, ∀ v ∈ S.comap P.mulVecLin, (a g).mulVec v ∈ S.comap P.mulVecLin := by
    intro g hg v hv
    rw [mem] at hv ⊢
    rw [H g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key]
    exact hS g hg _ hv
  rcases hirr _ hst with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have h2 : Q.mulVec v ∈ S.comap P.mulVecLin := by rw [mem, key]; exact hv
    rw [h0, Submodule.mem_bot] at h2
    rw [Submodule.mem_bot, ← key v, h2, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have h2 : Q.mulVec v ∈ S.comap P.mulVecLin := by rw [h1]; exact Submodule.mem_top
    rwa [mem, key] at h2

theorem UpperTheory.Reformulated.B.G5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ}
    {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R),
    (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
      UpperTheory.V.U3.MatIrr U a → UpperTheory.V.U3.MatIrr U a' := by
  intro G R _ _ m U a a' h H hirr
  exact UpperTheory.Reformulated.B.G5.irr_conj _ _ (Units.mul_inv h) H hirr
