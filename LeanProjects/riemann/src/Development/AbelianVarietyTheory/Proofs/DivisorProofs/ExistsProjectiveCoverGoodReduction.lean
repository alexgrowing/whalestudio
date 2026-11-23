import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTriangularFramesGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFramesOnSmoothCurvesStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagLines

theorem main : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (c : O.s.Comp) (P : Finset ℕ) (M : O.LatModel P c)
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
  intro hP2 hPH D O hO c P M q _ hqP hqd
  obtain ⟨W, a, b, hp, hs, hF⟩ := GlobalTheory.T.exists_triangular_frames_good_primes hP2 hPH D O hO c P M q hqP hqd
  refine ⟨W, a, b, hp, hs, fun k _ _ _ C _ _ hC g G _ _ i φ hφ β hβ τ => ?_⟩
  exact GlobalTheory.T.triangular_frames_on_smooth_curves O.s.T.Z.t O.s.T.Z.s (intEmb O.κ.c τ) q b a (O.S.Dw.mult τ)
    (fun m => (M.line P (.inl (τ, m))).B) (fun m => (M.line P (.inl (τ, m))).isLB) (hF τ) k C hC g G i φ hφ β hβ

end GlobalTheory.FlagLines
