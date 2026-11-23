import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.AdmissibleParameterJoins
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

section One

variable {D : D7} (L : SizeData₂ D)

theorem prod_gTypes : (∏ g ∈ L.gTypes, (g : ℝ)) = (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by
  unfold SizeData₂.gTypes
  rw [Finset.prod_pair D.host.g_ne]

theorem x_pos : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (x_pos L).le _)

theorem one_le_a : 1 ≤ L.sc.a := by
  unfold Scale.a
  have h1 : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have h2 := one_le_b L
  nlinarith

theorem La_nonneg (hS : SizeQD L) : 0 ≤ L.La := by
  unfold SizeData₂.La
  have h1 := one_le_a L
  have h2 : 1 ≤ D.host.rdE := hS.2.2.2.2.2.2.1
  exact Real.log_nonneg (by nlinarith)

end One

section Mono

variable {D : D7} (L : SizeData₂ D)

theorem degree_weight_bound_mono {C C' : ℝ} (hC : C ≤ C') (h : LocalQuadraticParts.adm11 D L C) : LocalQuadraticParts.adm11 D L C' := by
  have hB := mul_le_mul_of_nonneg_right hC (Formalism.MainNotions.loss_bound_nonneg L)
  exact fun u j hj => ⟨(h u j hj).1.trans hB, (h u j hj).2.trans hB⟩

end Mono

section Link

variable {eps : ℝ} (Fm : FamP eps)

structure DivisionSideHypotheses (Cin CF Csz0 : ℝ) : Prop where
  a1 : Ev Fm fun x hx i => LocalQuadraticParts.adm1 (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).p0
  a1s : Ev Fm fun x hx i => LocalQuadraticParts.PeterssonMetricHypotheses (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).amb
  a2 : Ev Fm fun x _ i => LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i)
  a3 : ∃ C, Ev Fm fun x _ i => LocalQuadraticParts.adm3 (Fm.D x i) (Fm.L x i) (Fm.X x i) C
  a4 : ∃ C, Ev Fm fun x _ i => LocalQuadraticParts.OrthonormalBoundsChoice (Fm.D x i) (Fm.L x i) C Cin
  a6 : ∃ C, Ev Fm fun x _ i => LocalQuadraticParts.adm6 (Fm.D x i) (Fm.L x i) C
  a6c : ∃ C, Ev Fm fun x _ i => LocalQuadraticParts.LogLambdaEstimatesOnComponents (Fm.D x i) (Fm.L x i) (Fm.X x i) C
  a6h : Ev Fm fun x _ i => LocalQuadraticParts.ConjugateLowerBound (Fm.D x i) (Fm.L x i) (Fm.X x i) Csz0
  a7 : Ev Fm fun x _ i => LocalQuadraticParts.adm7 (Fm.D x i) (Fm.L x i) Csz0
  a7r : Ev Fm fun x _ i => LocalQuadraticParts.KernelRationality (Fm.D x i)
  a9 : Ev Fm fun x hx i => Rows.AIntegral (Fm.D x i).what₂ ∧ (Fm.ex x hx i).p0.s.AIntegral
  twist_bounds_eight_to_ten : ∃ CT, Ev Fm fun x hx i => LocalQuadraticParts.adm8 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Fm.ex x hx i).p0 CF CT ∧
    LocalQuadraticParts.adm10 (Fm.D x i) (Fm.ex x hx i).p0 CT
  a11 : ∃ C, Ev Fm fun x _ i => LocalQuadraticParts.adm11 (Fm.D x i) (Fm.L x i) C
  a12 : Ev Fm fun x _ i => LocalQuadraticParts.adm12 (Fm.D x i) (Fm.L x i)
  a13 : Ev Fm fun x _ i => LocalQuadraticParts.adm13 (Fm.D x i)
  a33 : Ev Fm fun x _ i => LocalQuadraticParts.ZeroGainAbove (Fm.L x i)

end Link

end Formalism.MainNotions.DIV

end
