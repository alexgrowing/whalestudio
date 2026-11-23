import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagPointTangentDualNumberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsChartIndependenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTangentVectorsCompatStatement

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibLie

theorem exists_lieBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (y : GlobalTheory.ShFam.Pad.FlagPt Z Qb) (K : Type) [Field K] [NumberField K] (ι : K →+* Qb) (jF : c.F →+* K) (yK : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ GlobalTheory.Toroidal.gen Z) (uK : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ Z.t.G.left)), ι.comp jF = y.fK → ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ yK = y.y → yK ≫ GlobalTheory.Toroidal.genStr Z = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap jF → (∀ τ i, y.u τ i = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK τ i) → ∀ (P₀ : ReciprocityTheory.ChartRestriction.G.Out.PolAV (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (θ : P₀.A.left ⟶ Z.t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback P₀.A Z.t.G (yK ≫ GlobalTheory.Toroidal.genι Z) θ → ∀ n : ℕ, n = (GlobalTheory.ShFam.Pad.letters Dw).length → ∃ v : Fin n → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ P₀.A), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v ∧ ∀ (k : Fin n) (x : GlobalTheory.ShFam.Pad.Letter Dw), (GlobalTheory.ShFam.Pad.letters Dw)[(k : ℕ)]? = some x → (v k).left ≫ θ = uK x.1 x.2 := by
  intro E _ _ _ H Dw l Xo c Z y K _ _ ι jF yK uK _ hy _ hu P₀ θ hθ n hn
  subst hn
  have hx : y.y ≫ GlobalTheory.Toroidal.genι Z = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ (yK ≫ GlobalTheory.Toroidal.genι Z) := by
    rw [← Category.assoc, hy]
  set L := GlobalTheory.ShFam.Pad.letters Dw with hL
  have hA := GlobalTheory.T.toroidal_flag_point_tangent_dual_number Z y
  rw [hx] at hA
  have htan : ∀ j : Fin L.length, Formalism.L2.Pj.IsTanAtG Z.t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ (yK ≫ GlobalTheory.Toroidal.genι Z))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK (L.get j).1 (L.get j).2) := by
    intro j
    rw [← hu, ← hx]
    exact y.tan _ _
  have hA' : ∀ w, Formalism.L2.Pj.IsTanAtG Z.t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ (yK ≫ GlobalTheory.Toroidal.genι Z)) w →
      ∃! a : Fin L.length → Qb, Formalism.L2.Pj.IsCombAtG Z.t (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ι ≫ (yK ≫ GlobalTheory.Toroidal.genι Z))
        (fun j => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ uK (L.get j).1 (L.get j).2) a w := by
    intro w hw
    simpa only [hu] using hA w hw
  obtain ⟨hKt, hKb⟩ := GlobalTheory.T.tangent_vectors_chart_independence Z.t ι (yK ≫ GlobalTheory.Toroidal.genι Z) (fun j => uK (L.get j).1 (L.get j).2) htan hA'
  obtain ⟨v, hv, hvθ⟩ := GlobalTheory.T.group_pullback_tangent_vectors_compat Z.t (yK ≫ GlobalTheory.Toroidal.genι Z) P₀.A θ hθ _ hKt hKb
  refine ⟨v, hv, fun k x hk => ?_⟩
  rw [hvθ k]
  have : L.get k = x := by
    rw [List.get_eq_getElem]
    exact Option.some_injective _ ((List.getElem?_eq_getElem k.2).symm.trans hk)
  rw [this]

end GlobalTheory.FibLie
