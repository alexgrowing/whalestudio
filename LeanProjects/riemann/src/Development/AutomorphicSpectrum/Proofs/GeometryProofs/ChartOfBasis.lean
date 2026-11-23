import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.GermInh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem chart_of_basis (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {n : ℕ}
    (tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (h : GlobalTheory.ChartCompare.IsTanBasisG t x0 tg) :
    ∃ (G : Germ.FGLaw S (Fintype.card (Fin n))) (A : Germ.OAct (𝓞 E) G)
      (tg' : Fin (Fintype.card (Fin n)) → (Sp (DualNumber S) ⟶ t.G.left)) (x : ∀ m, jOG x0 _ m 1 ⟶ t.G),
      IsChartG t x0 _ G.F A.act tg' (fun l j => if l = j then 1 else 0) x ∧ (∀ l, IsTanAtG t x0 (tg' l)) ∧
      ∀ w, IsTanAtG t x0 w → ∃! a : Fin (Fintype.card (Fin n)) → S, IsCombAtG t x0 tg' a w := by
  obtain ⟨d, G, A, uvec, x, rfl, hu, hc⟩ := GlobalTheory.ChartData.exists_isChartG_of_basis E H X0 t S x0 _ tg h.1 h.2
  let e := Fintype.equivFin (Fin n)
  refine ⟨G, A, fun i => tg (e.symm i), x, ⟨hc.zero, hc.trunc, hc.law, hc.act, fun l => ?_, fun v => ?_⟩,
    fun l => h.1 _, fun w hw => ?_⟩
  · have := hc.tan (e.symm l)
    convert this using 2 with j
    rw [hu]; simp [e, Fin.ext_iff, eq_comm]
  · refine ⟨v, fun j => by simp, fun a ha => funext fun j => by simpa using ha j⟩
  · obtain ⟨a, ha, hu⟩ := h.2 w hw
    refine ⟨fun i => a (e.symm i), ha, fun b hb => ?_⟩
    have := hu (fun l => b (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hb)
    funext i; rw [← this]; simp

theorem germ_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0), ∃ d, Nonempty (GermAt t x d) := by
  intro E _ _ _ H _ hs X0 t hp S _ _ x0
  obtain ⟨n, tg, h⟩ := GlobalTheory.ChartDataChecks.premises_met t x0
  obtain ⟨G, A, tg', x, hc, ht, hb⟩ := chart_of_basis t x0 tg h
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, -, htr, hfa, had, -⟩ := GermB.frameSt_holds E H X0 t S x0 _ G A _ tg' _ x hc
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg' _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨_, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg', hc, ht, hb, hfr, htr, hfa⟩⟩⟩

section One
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

end One

end GlobalTheory.CompanionTheory.Ar.Conj.GermInh
