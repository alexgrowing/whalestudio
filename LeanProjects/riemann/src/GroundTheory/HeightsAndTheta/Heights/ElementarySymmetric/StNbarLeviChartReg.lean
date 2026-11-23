import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartFam
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}

def regNbarQ (H : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B p q : ℕ) (t : ℝ) :
    HermLine ι :=
  smoothRep (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg H B + (p : ℤ) • D.a') fun z =>
      (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)

def NbarLeviChartReg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (S : LogLogRegularisationSetting M D.Xo (muLine H)), S.IsTied → ∀ (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin S.R.N, M.proj z ∈ S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel M (S.R.chart k) z w v ∧
        levi (fun y => Real.log ((regNbarQ H M S B p q t).h y)) z w =
          q * levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

theorem NbarLeviChart.of_reg (h : NbarLeviChartReg.Statement) : LowerBoundFree.NbarLeviChart.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hs z hz w hw k hk
  exact h II Ψ K ι Ω E D X.H X.M X.S X.S_tied B p q t hs z hz w hw k hk

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem NbarLeviChartReg.hyps_inhabited :
    (projLineFamilySetting II hII).S.IsTied ∧
    ∃ t : ℝ, 0 < t ∧ (projLineFamilySetting II hII).M.atlas.Smooth ((projLineFamilySetting II hII).S.regWeight t) ∧
    LowerBoundFree.Line.discL 0 ∈ mcPts (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y) ∧
    IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (LowerBoundFree.Line.lineData II hII).y)
      (LowerBoundFree.Line.discL 0) LowerBoundFree.Line.velL ∧
    ∃ k : Fin (projLineFamilySetting II hII).S.R.N,
      (projLineFamilySetting II hII).M.proj (LowerBoundFree.Line.discL 0) ∈ (projLineFamilySetting II hII).S.R.mid k :=
  ⟨(projLineFamilySetting II hII).S_tied, NbarLeviChartFam.hyps_inhabited II hII⟩

end Line

end GroundTheory.Heights₂.Heights.NineStatements
