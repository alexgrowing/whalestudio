import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mat_cancel_left {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (B M M' : Matrix n n R) (hB : B.det ∈ nonZeroDivisors R) (h : B * M = B * M') : M = M' := by
  have h2 : B.det • M = B.det • M' := by
    have e : ∀ N : Matrix n n R, B.det • N = B.adjugate * (B * N) := fun N => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, h]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  have h4 : (M i j - M' i j) * B.det = 0 := by rw [sub_mul, mul_comm (M i j), mul_comm (M' i j), h3, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hB) _ h4)

theorem bas_map_cancel_left : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (C : Type) [CommRing C] (F : bk.DS bk.ρ₀ →+* C), F (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors C → ∀ M M' : Matrix (Fin d) (Fin d) C, ht.bas.map F * M = ht.bas.map F * M' → M = M' := by
  intro l _ K bk d ρ τ s ht C _ F hE M M' h
  set G : bk.S →+* C := F.comp (toDisc l (X : bk.S) bk.ρ₀) with hG
  have hbas : ht.bas.map F = s.X.map G * ht.Z.map F := by
    rw [bas, Matrix.map_mul, Matrix.map_map]; rfl
  have hl : IsUnit (G (l : bk.S)) := by
    rw [map_natCast]
    have := (isUnit_l_disc l (X : bk.S) bk.ρ₀).map F
    rwa [map_natCast] at this
  have hc : G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ∈ nonZeroDivisors C := by
    rw [map_mul, map_pow, map_pow]
    exact Submonoid.mul_mem _ (Submonoid.pow_mem _ hl.mem_nonZeroDivisors _) (Submonoid.pow_mem _ hE _)
  have hdet : (s.X.map G).det * (s.X'.map G).det = G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ^ d := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, s.X_mul, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero G),
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hX : (s.X.map G).det ∈ nonZeroDivisors C :=
    (mul_mem_nonZeroDivisors.1 (hdet ▸ Submonoid.pow_mem _ hc _)).1
  have hZ : IsUnit (ht.Z.map F).det := by
    have := ht.Z_unit.map F.mapMatrix
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  refine mat_cancel_left _ M M' ?_ h
  rw [hbas, Matrix.det_mul]
  exact Submonoid.mul_mem _ hX hZ.mem_nonZeroDivisors

end GlobalTheory.BSP.Height
