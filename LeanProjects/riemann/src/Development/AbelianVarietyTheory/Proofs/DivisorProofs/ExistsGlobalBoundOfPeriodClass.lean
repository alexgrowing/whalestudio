import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem exists_bound_glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F), K.Rich → ∀ (r : Real K s σ) (f : Form s) (per : Λ →+ Hol F.V), r.coef.pull1 (Form.cl s f) = K.perCl per → ∃ (q : GlobalTheory.CatCoh.C0 K.Oc) (G : Tot I g → ℂ), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 ∧ AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, Hol.fn (W := K.W k) (q (K.triv k)) p = G p) ∧ ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → G (F.shift l p) = G p + (per l).fn p.1 := by
  intro I _ g Λ _ F B _ X s σ K hK r f per hc
  have hc' : GlobalTheory.CatCoh.H1.mk K.Oc (r.coef.pullbackOneCocycle f.1) = GlobalTheory.CatCoh.H1.mk K.Oc (K.perZ per) := hc
  obtain ⟨q, hq⟩ := GlobalTheory.CatCoh.H1.mk_eq_mk.1 hc'
  have key : ∀ (l : Λ) (k k' : K.K) (h : K.le l k' k),
      Charts.sh h (q (K.triv k)) = q (K.triv k') + K.cst k' (per l) := by
    intro l k k' h
    have e := congrFun (congrFun (congrFun hq (K.triv k)) (K.triv k')) (Charts.ptHom (K.triv k') h)
    have h0 : (r.coef.pullbackOneCocycle f.1).1 _ _ (Charts.ptHom (K.triv k') h) = 0 :=
      f.2 (r.functor.map (Charts.ptHom (K.triv k') h)) rfl rfl
    rw [GlobalTheory.CatCoh.amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, h0, zero_sub] at e
    change q (K.triv k') - Charts.sh h (q (K.triv k)) = -K.cst k' (per l) at e
    linear_combination -e
  obtain ⟨G, hGa, hG, hsh, -⟩ := Charts.glue K hK (fun k ↦ q (K.triv k))
    (fun k k' h ↦ by rw [key 0 k k' h, map_zero, map_zero, add_zero])
  exact ⟨q, G, hq, hGa, hG, fun l p hp ↦ hsh l (per l) (fun k k' h ↦ key l k k' h) p hp⟩

end GlobalTheory.AnPer.Charts
