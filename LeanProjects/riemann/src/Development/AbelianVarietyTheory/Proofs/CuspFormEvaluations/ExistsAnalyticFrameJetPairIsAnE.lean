import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReadingStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJetsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem jetMap_psum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el) (n m : ℕ) (xs : Fin n → (jO y g m n ⟶ Xo.univ.t.G))
    (Λ : Fin n → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hx : ∀ i, Φ.toAnFr.JetMap m (xs i).left (Λ i))
    (I : Finset (Fin n)) :
    Φ.toAnFr.JetMap m (psum Xo.univ.t.G xs I).left (∑ i ∈ I, Λ i) := by
  obtain ⟨-, h1, hmul, -⟩ := GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ n m
  have key : ∀ L : List (Fin n), Φ.toAnFr.JetMap m
      (L.foldr (fun k acc => padd Xo.univ.t.G (xs k) acc) (pzero Xo.univ.t.G (jO y g m n))).left
      (L.map Λ).sum := by
    intro L
    induction L with
    | nil => exact h1
    | cons k L ih => exact (hmul _ _ _ _ (hx k) ih).1
  have hs : (((List.finRange n).filter (fun x => decide (x ∈ I))).map Λ).sum = ∑ i ∈ I, Λ i := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  rw [← hs]
  exact key _

theorem exists_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have h : ∀ m, ∃ τ : FrTy y g Φ.jx m, τ.IsGen ∧ Φ.toAnFr.JetRd m
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) τ (psumL 2 g) := by
    intro m
    refine GlobalTheory.T.exists_generator_jet_reading _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 m _
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) (psumL 2 g) ?_
    intro I
    refine jetMap_psum Φ 2 m _ (fun i => LinearMap.proj i) ?_ I.down
    have h0 := (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 2 m).1
    intro i
    fin_cases i
    · exact h0 0
    · exact h0 1
  choose e he using h
  exact ⟨e, he⟩

end GlobalTheory.AnVal
