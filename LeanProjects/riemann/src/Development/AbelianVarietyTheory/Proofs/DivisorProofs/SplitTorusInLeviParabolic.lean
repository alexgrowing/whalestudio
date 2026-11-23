import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementPreservesWittColumnSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameEigenvectorColumnFormStatement
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorusCent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem swap (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : IsWittFrame σ J Y X :=
  ⟨hW.yy, hW.xx, yx h hJ hW, fun z h1 h2 h3 => hW.aniso z h2 h1 h3⟩

theorem levi_swap (S : Finset (Fin r)) : levi σ J Y X S = levi σ J X Y S := by
  simp only [levi, inf_comm]

theorem comm_block (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {S : Finset (Fin r)}
    (hS : ∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) {g : GAd σ J} (hg : g ∈ levi σ J X Y S) (d : Fin r → AF F ⊗[F] E)
    (hd : ∀ k ∉ S, d k = 0) :
    (matHom _ σ J g).1 * (adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J)) =
      adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 := by
  have e1 : (matHom _ σ J g).1 * adMat F X * diagonal d = adMat F X * diagonal (fun k =>
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * d k) := by
    ext i k
    rw [mul_diagonal, mul_diagonal]
    by_cases hk : k ∈ S
    · have := congrFun (GlobalTheory.T.levi_element_preserves_witt_column_span h hJ hW hS hg k hk) i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_apply, this]
      ring
    · simp [hd k hk]
  have e2 : diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 =
      diagonal (fun k => (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * d k) *
        adMat F (cT (σ : E →+* E) Y * J) := by
    ext k i
    rw [Matrix.mul_assoc, diagonal_mul, diagonal_mul]
    by_cases hk : k ∈ S
    · have hg' : g⁻¹ ∈ levi σ J Y X S := by rw [levi_swap]; exact inv_mem hg
      rw [GlobalTheory.T.witt_frame_eigenvector_column_form h hJ hW _ (GlobalTheory.T.levi_element_preserves_witt_column_span h hJ (swap h hJ hW) hS hg' k hk) i]
      ring
    · simp [hd k hk]
  calc (matHom _ σ J g).1 * (adMat F X * diagonal d * adMat F (cT (σ : E →+* E) Y * J))
      = ((matHom _ σ J g).1 * adMat F X * diagonal d) * adMat F (cT (σ : E →+* E) Y * J) := by
        simp only [Matrix.mul_assoc]
    _ = adMat F X * (diagonal d * adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) := by
        rw [e1, e2]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem centre_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {S : Finset (Fin r)}, (∀ k ∈ S, ∀ i, i ≤ k → i ∈ S) → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, (∀ k ∉ S, l k = 1) → IsIdTorusElt σ J X Y l a → a ∈ levi σ J X Y S ∧ ∀ m ∈ levi σ J X Y S, a * m = m * a := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW S hS l a hl ha
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((l (Fin.castLE k.2 i) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((l (Fin.castLE k.2 i))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ (l (Fin.castLE k.2 i)))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ (l (Fin.castLE k.2 i)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · apply matHom_injective
    apply Units.ext
    have hd1 : ∀ k ∉ S, ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = 0 := fun k hk => by simp [hl k hk]
    have hd2 : ∀ k ∉ S, (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = 0 := fun k hk => by simp [hl k hk]
    have c1 := comm_block h hJ hW hS hm _ hd1
    have c2 := comm_block h hJ (swap h hJ hW) hS (by rwa [levi_swap]) _ hd2
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq h hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, c1, c2]

end GlobalTheory.IdTorusCent

end
