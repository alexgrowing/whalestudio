import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarChartSemiposFam
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarLeviChartFam.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (X : ComponentFamilySetting D) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v ∧
        levi (fun y => Real.log ((X.NbarQ B p q t).h y)) z w =
          q * levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k (X.M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem NbarLeviChartFam.hyps_inhabited :
    ∃ t : ℝ, 0 < t ∧ (projLineFamilySetting II hII).M.atlas.Smooth ((projLineFamilySetting II hII).S.regWeight t) ∧
    LowerBoundFree.Line.discL 0 ∈ mcPts (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y) ∧
    IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y)
      (LowerBoundFree.Line.discL 0) LowerBoundFree.Line.velL ∧
    ∃ k : Fin (projLineFamilySetting II hII).S.R.N,
      (projLineFamilySetting II hII).M.proj (LowerBoundFree.Line.discL 0) ∈ (projLineFamilySetting II hII).S.R.mid k := by
  obtain ⟨t, -, ht, hs, -⟩ := NineStatements.NbarChartSemiposFam.hyps_of_setting (projLineFamilySetting II hII) one_pos
  exact ⟨t, ht, hs, LowerBoundFree.Line.discL_mem 0, LowerBoundFree.Line.isConeTangent_velL, (0 : Fin 2),
    LowerBoundFree.Line.projL_discL_mem_mid⟩

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
