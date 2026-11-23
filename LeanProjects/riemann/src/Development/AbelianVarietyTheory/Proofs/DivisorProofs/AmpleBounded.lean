import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedOfIsAlgPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseClosedPointsBoundedHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeightStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.DenseBoundedHeight

theorem ample_bounded : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp, ∃ S : Set (O.var c).X, (∀ b ∈ S, IsClosed ({b} : Set (O.var c).X)) ∧ Dense S ∧ ∃ C : ℝ, ∀ b ∈ S, |(O.met.ab c).ht b| ≤ C := by
  intro hP hH D O hO c
  obtain ⟨Ca, hCa⟩ := GlobalTheory.T.abelian_height_bounded_below hP hH D O hO c
  obtain ⟨S, hSc, hSd, Cb, hCb⟩ := GlobalTheory.T.dense_closed_points_bounded_height hP hH D O hO c
  refine ⟨S, hSc, hSd, max Ca Cb, fun b hb => abs_le.2 ⟨?_, ?_⟩⟩
  · have := hCa b (hSc b hb)
    have : Ca ≤ max Ca Cb := le_max_left _ _
    linarith
  · exact (hCb b hb).trans (le_max_right _ _)

theorem htUpSt : Hypotheses2 → HypothesesH → HtUpSt := by
  intro hP hH D O hO _ A T H h c
  obtain ⟨S, hSc, hSd, C1, hC1⟩ := ample_bounded hP hH D O hO c
  choose Cx hCx using GlobalTheory.T.root_height_le_abelian_height hP hH D O hO h.mdl c
  set M : ℝ := ∑ x, |Cx x| * (|C1| + 1) with hM
  have hb : ∀ b ∈ S, ∀ x, |(O.root0 c ∅ x).ht b| ≤ |Cx x| * (|C1| + 1) := fun b hbS x => by
    have h1 := hCx x b (hSc b hbS)
    have h2 : |(O.met.ab c).ht b| ≤ |C1| := (hC1 b hbS).trans (le_abs_self _)
    calc |(O.root0 c ∅ x).ht b| ≤ Cx x * (|(O.met.ab c).ht b| + 1) := h1
      _ ≤ |Cx x| * (|(O.met.ab c).ht b| + 1) := by gcongr; exact le_abs_self _
      _ ≤ |Cx x| * (|C1| + 1) := by gcongr
  have hP' : ∀ b ∈ S, |(O.met.ab c).ht b| ≤ max |C1| M ∧
      ∀ u : D.what₂.Tau → Fin O.N → ℝ, |O.htWt (O.root0 c ∅) u b| ≤ max |C1| M * ‖u‖ := fun b hbS => by
    refine ⟨((hC1 b hbS).trans (le_abs_self _)).trans (le_max_left _ _), fun u => ?_⟩
    show |-(∑ x, u x.1 x.2 * (O.root0 c ∅ x).ht b)| ≤ _
    rw [abs_neg]
    calc |∑ x, u x.1 x.2 * (O.root0 c ∅ x).ht b| ≤ ∑ x, |u x.1 x.2 * (O.root0 c ∅ x).ht b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, ‖u‖ * (|Cx x| * (|C1| + 1)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          have hu : |u x.1 x.2| ≤ ‖u‖ := by
            have a1 : ‖u x.1 x.2‖ ≤ ‖u x.1‖ := norm_le_pi_norm (u x.1) x.2
            have a2 : ‖u x.1‖ ≤ ‖u‖ := norm_le_pi_norm u x.1
            rw [Real.norm_eq_abs] at a1
            exact a1.trans a2
          exact mul_le_mul hu (hb b hbS x) (abs_nonneg _) (norm_nonneg _)
      _ = M * ‖u‖ := by rw [← Finset.mul_sum, mul_comm]
      _ ≤ max |C1| M * ‖u‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  refine ⟨{y | GlobalTheory.ShFam.Pad.compPt O.s y = c ∧ baseOn O.Φ c y ∈ S}, ?_, max |C1| M, ?_⟩
  · refine (h.aux.dense c _).2 ⟨fun y hy => hy.1, ?_⟩
    have e : baseOn O.Φ c '' {y | GlobalTheory.ShFam.Pad.compPt O.s y = c ∧ baseOn O.Φ c y ∈ S} = S := by
      ext b
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy.2
      · intro hbS
        obtain ⟨y, hy1, hy2⟩ := OnModel.exists_baseOn c (hSc b hbS)
        exact ⟨y, ⟨hy1, hy2 ▸ hbS⟩, hy2⟩
    exact (congrArg Dense e).mpr hSd
  · rintro y ⟨hyc, hyS⟩
    have key : ∀ k, k = c → |(O.met.ab k).ht (baseOn O.Φ k y)| ≤ max |C1| M ∧
        ∀ u : D.what₂.Tau → Fin O.N → ℝ, |O.htWt (O.root0 k ∅) u (baseOn O.Φ k y)| ≤ max |C1| M * ‖u‖ := by
      rintro k rfl
      exact hP' _ hyS
    obtain ⟨k1, k2⟩ := key _ hyc
    refine ⟨?_, fun u => ?_⟩
    · exact (le_of_eq (congrArg abs (h.ht.hA y))).trans k1
    · exact (le_of_eq (congrArg abs (h.ht.h0 u y))).trans (k2 u)

end GlobalTheory.DenseBoundedHeight

end
