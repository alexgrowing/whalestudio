import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveCoverGoodReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_cover_good_reduction : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (P : Finset ℕ) (M : O.LatModel P c)
  (q : ℕ) [Fact q.Prime], q ∉ P → ¬ q ∣ (discr D.host.E).natAbs →
  ∃ (W : Scheme.{0}) (a : W ⟶ M.V.X) (b : W ⟶ O.s.T.Z.X), IsProjOver (a ≫ M.V.p) ∧ Surjective a ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
      IsSmoothProjCurve k C → ∀ (g : C ⟶ W) (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 D.host.E) G)
      (φ : G.left ⟶ O.s.T.Z.t.G.left), IsActPull i O.s.T.Z.t.act (g ≫ b) φ →
      ∀ β : 𝓞 O.κ.c.F →+* k, g ≫ b ≫ O.s.T.Z.s = strHom k C ≫ spMap β → ∀ τ : D.host.E →+* ℂ,
        (∀ n ≤ O.S.Dw.mult τ,
          ∑ m ∈ Finset.range n, degLB k ((M.line P (.inl (τ, m))).B.pull (g ≫ a)) ∈ subDegs k (Lie G)) ∧
        deg k (lieSub i (scal C (β.comp (intEmb O.κ.c τ)))) =
          ∑ m ∈ Finset.range (O.S.Dw.mult τ), degLB k ((M.line P (.inl (τ, m))).B.pull (g ≫ a)) := by
  first | exact @GlobalTheory.FlagLines.main | exact GlobalTheory.FlagLines.main | (intros; apply GlobalTheory.FlagLines.main <;> assumption)
