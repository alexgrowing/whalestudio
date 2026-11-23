import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN
import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedDegreePolynomialAntisymmetricStatement
import Development.WeilBound.CoreStatements.FlagImmersions.HasPerConj
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsModelOfEq
import Development.WeilBound.CoreStatements.FlagImmersions.NormDetEq
import Development.WeilBound.CoreStatements.FlagImmersions.PerCoord
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsRightInv
import Development.WeilBound.CoreStatements.FlagImmersions.RankLem
import Development.WeilBound.CoreStatements.FlagImmersions.EqZeroOfTri
import Development.WeilBound.CoreStatements.FlagImmersions.GenRigidOf
import Development.WeilBound.CoreStatements.FlagImmersions.CountableBall
import Development.WeilBound.CoreStatements.FlagImmersions.Imports
import Development.WeilBound.CoreStatements.CentralCharts.FlagImmersion

noncomputable section

namespace AnalyticReference.Deg

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB

theorem eval_formPoly_none {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → Option σ) → ℝ) (c : σ → ℝ) :
    eval (fun o : Option σ => o.elim 0 c) (formPoly n a) =
      eval c (formPoly n fun w => a fun j => some (w j)) := by
  have h : ∀ Q : MvPolynomial (Option σ) ℝ,
      eval c (aeval (fun o : Option σ => o.elim (0 : MvPolynomial σ ℝ) X) Q) =
        eval (fun o : Option σ => o.elim 0 c) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p o hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases o <;> simp
  rw [← h, killNone_formPoly]

theorem eval_antisymDelta_pos {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Ψ × Fin N → ℝ)
    (h : ∀ τ (i k : Fin N), i < k → lam (τ, k) < lam (τ, i)) :
    0 < eval lam (GroundTheory.Heights₂.Heights.antisymDelta Ψ N) := by
  simp only [GroundTheory.Heights₂.Heights.antisymDelta, map_prod, map_sub, eval_X]
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
  exact sub_pos.2 (h τ a b (Finset.mem_Ioi.1 hb))

end AnalyticReference.Deg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff

theorem AnalyticReference.gap_polynomial_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ), (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → 0 < MvPolynomial.eval (fun a => (gapN ν a : ℝ)) A.Sys.degPoly := by
  intro hG E _ _ _ H D Xo l c Y _ hp _ G A ν hν
  classical
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hU := AnalyticReference.unif_of RootFieldNumerics.locPer RootFieldNumerics.transport RootFieldNumerics.frameVals (RootFieldNumerics.perMat_of RootFieldNumerics.perCoord RootFieldNumerics.matStep)
    (RootFieldNumerics.flagImm_of RootFieldNumerics.rankLem) (RootFieldNumerics.countGen_of (RootFieldNumerics.genRigid_of RootFieldNumerics.frameVals)) hG (le_add_right hp) G A
  have hdim : Top.dimFl (CMType H) (D.p + D.q) = GroundTheory.Heights₂.Heights.antisymDegree (CMType H) (D.p + D.q) := by
    simp [Top.dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]
  obtain ⟨v, hv, hE⟩ := GlobalTheory.T.uniformised_degree_polynomial_antisymmetric hI (CMType H) (D.p + D.q) D.p _ (A.Sys.comap some) (Nat.le_add_right _ _) hdim hU
  let lam : RootIx D → ℝ := fun p => (ν p : ℝ)
  have hgap : (fun a => (gapN ν a : ℝ)) = fun o : Option (RootIx D) => o.elim 0 (PB.gap lam) := by
    funext o
    cases o with
    | none => simp [gapN]
    | some p =>
      simp only [gapN, Option.elim, PB.gap, PB.gapX, map_sub, MvPolynomial.eval_X, lam]
      split_ifs <;> simp
  have hΔ := AnalyticReference.Deg.eval_antisymDelta_pos (Ψ := CMType H) (N := D.p + D.q) lam
    (fun τ i k hik => by
      show ((ν (τ, k) : ℤ) : ℝ) < (ν (τ, i) : ℤ)
      exact_mod_cast hν τ i k hik)
  have h1 := congrArg (MvPolynomial.eval lam) hE
  rw [PB.eval_toWt_gap, map_mul, MvPolynomial.eval_C] at h1
  rw [hgap, PB.AnSys.degPoly, AnalyticReference.Deg.eval_formPoly_none]
  exact lt_of_lt_of_eq (mul_pos hv hΔ) h1.symm
