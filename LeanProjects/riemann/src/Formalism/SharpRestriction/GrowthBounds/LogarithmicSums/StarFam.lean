import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNum
import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.StarNumB

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.St

theorem star_fam {eps : ℝ} (Fm : FamP eps) (K : Consts) (hK : K.Nonneg) (C31 Ce Cm : ℝ) (hC31 : 0 < C31) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C ≥ C0, ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i))
      (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)), AdmFam Fm K X Y C31 Ce Cm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, StarAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) := by
  have heps : 0 < eps := by
    obtain ⟨i0⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i0]
    exact (Fm.L 0 i0).sc.eps_pos
  refine ⟨max (CStar eps K C31) 0, le_max_right _ _, fun C hC X Y hAdm => ?_⟩
  obtain ⟨x2, -, hx2⟩ := hAdm (eps / 48) (by linarith)
  obtain ⟨x3, hx3⟩ := Filter.eventually_atTop.1
    ((numStar_ev eps K hK C31 hC31).and (B.facts_ev eps K hK C31 hC31))
  refine ⟨max (max x2 x3) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 := le_max_left (max x2 x3) (Fm.x1 + 1)
  have h2 := le_max_right (max x2 x3) (Fm.x1 + 1)
  have h3 := le_max_left x2 x3
  have h4 := le_max_right x2 x3
  have hxx1 : Fm.x1 < x := by linarith
  have hP := Fm.params x hxx1 i
  have hS := Fm.sizes x hxx1 i
  obtain ⟨A1, -, -, -, A5, -⟩ := hx2 x (by linarith) i
  have hx3' := hx3 x (by linarith)
  have hF := hx3'.2 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hxx1) (Fm.L_eps x i) hS hP A5
  have hN := hx3'.1 (Fm.D x i) (Fm.L x i) (Fm.L_x x i hxx1) (Fm.L_eps x i) hS hP _
    ⟨hF.hkQ, hF.hDII, hF.hbo⟩ C (le_trans (le_max_left _ _) hC)
  exact starAll_of (X x i) hK hP A1 hC31 hN

end Formalism.MainNotions.AuxBlock8.Pf.St

end
