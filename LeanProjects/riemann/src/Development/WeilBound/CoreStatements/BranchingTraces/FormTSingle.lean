import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace PositivityTheory.UnitaryDecomposition

open Formalism.REAL Formalism.MainNotions.S Formalism.MainNotions.BridgeCSchur CompanionTheory.D.Upq.Sm

section

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

theorem u_mul (hU : IsURepOn (UJset ε) π) (g h : UJ ε) (x : H) : π (um (g * h)) x = π (um g) (π (um h) x) := by
  have := hU.1.2 _ (umat_mem g) _ (umat_mem h)
  exact DFunLike.congr_fun this x

theorem u_adj (hU : IsURepOn (UJset ε) π) (g : UJ ε) (x y : H) : ⟪π (um g) x, y⟫_ℂ = ⟪x, π (um g⁻¹) y⟫_ℂ := by
  have hy : y = π (um g) (π (um g⁻¹) y) := by
    rw [← u_mul hU, mul_inv_cancel]
    exact (DFunLike.congr_fun hU.1.1 y).symm
  conv_lhs => rw [hy]
  exact (LinearIsometry.mk (π (um g) : H →ₗ[ℂ] H) (hU.2.1 _ (umat_mem g))).inner_map_map x _

theorem repOn (hU : IsURepOn (UJset ε) π) : RepOn (PI.PhMeasCore.UH (Jm ε)) π where
  one_mem := (1 : UJ ε).2
  mul_mem a ha b hb := (indefiniteUnitaryMk ε a ha * indefiniteUnitaryMk ε b hb).2
  map_one := hU.1.1
  map_mul a ha b hb := hU.1.2 a ha b hb

theorem smT_act (hU : IsURepOn (UJset ε) π) (g : UJ ε) {x : Fin m → H} (hx : x ∈ SmT ε π) : actT π (um g) x ∈ SmT ε π := by
  intro c
  show IsSm (PI.PhMeasCore.UH (Jm ε)) π (∑ d, _)
  refine Finset.sum_induction _ _ (fun a b ha hb => IsSm.add ha hb) IsSm.zero fun d _ => ?_
  exact (IsSm.apply (repOn hU) (hx d) g.2).smul _

theorem smT_single {v : H} (hv : v ∈ PI.PhMeasCore.smoothVecs (Jm ε) π) (l : Fin m) : (Pi.single l v : Fin m → H) ∈ SmT ε π := by
  intro c
  by_cases h : c = l
  · subst h; simpa using hv
  · rw [Pi.single_eq_of_ne h]; exact IsSm.zero (G := PI.PhMeasCore.UH (Jm ε))

theorem formT_single (l : Fin m) (v : H) (x : Fin m → H) : formT ε (Pi.single l v) x = (if ε l then 1 else -1) * ⟪v, x l⟫_ℂ := by
  unfold formT
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [Pi.single_eq_of_ne hb, inner_zero_left, mul_zero]) (by simp), Pi.single_eq_same]

theorem actT_single (g : Matrix (Fin m) (Fin m) ℂ) (l c : Fin m) (v : H) : actT π g (Pi.single l v) c = g⁻¹ l c • π g v := by
  unfold actT
  rw [Finset.sum_eq_single l (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero, smul_zero]) (by simp), Pi.single_eq_same]

end

end PositivityTheory.UnitaryDecomposition
