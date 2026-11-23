import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.OfMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Pp

variable {R : Type} [CommRing R]

theorem isUp_iff (X : M4 R) : IsUp X ↔ X.BlockTriangular id := by
  unfold IsUp
  exact ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

theorem IsUp_mul {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  rw [isUp_iff] at hX hY ⊢
  exact hX.mul hY

theorem IsUp_adj {X : M4 R} (hX : IsUp X) : IsUp (adj X) := fun i j h => by
  rw [adj_apply, hX j.rev i.rev (Fin.rev_lt_rev.2 h), smul_zero]

theorem IsUp_inv {b : (M4 R)ˣ} (hb : IsUp (b : M4 R)) : IsUp ((b⁻¹ : (M4 R)ˣ) : M4 R) := by
  rw [isUp_iff] at hb ⊢
  haveI := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem IsUp_diag {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) : (X * Y) i i = X i i * Y i i := by
  rw [isUp_iff] at hX hY
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hX h, zero_mul]
    · rw [hY h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem upConj {a b X : M4 R} (hab : a * b = 1) (ha : IsUp a) (hb : IsUp b) (hX : IsUp X) :
    IsUp (a * X * b) ∧ ∀ i, (a * X * b) i i = X i i := by
  have hax : IsUp (a * X) := IsUp_mul ha hX
  refine ⟨IsUp_mul hax hb, fun i => ?_⟩
  rw [IsUp_diag hax hb, IsUp_diag ha hX]
  have h1 : a i i * b i i = 1 := by
    rw [← IsUp_diag ha hb, hab]
    simp
  calc a i i * X i i * b i i = X i i * (a i i * b i i) := by ring
    _ = X i i := by rw [h1, mul_one]

theorem adj_mul_self {u : M4 R} (h : IsGSp 1 u) : adj u * u = 1 := h.trans (one_smul _ _)

theorem mul_adj_self {u : M4 R} (h : IsGSp 1 u) : u * adj u = 1 := mul_eq_one_comm.1 (adj_mul_self h)

end UpperTheory.V.Ws.Pp
