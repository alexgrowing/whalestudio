import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPower
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
open IsDedekindDomain

namespace GlobalTheory.CovHt.RootFirst

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem prod_expo_single {M : Type} [CommGroup M] (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → M) (b : ℕ → Bool) (R : Option ℝ)
    (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (Finsupp.single (b, R, .inl (τ, (k : ℕ))) 1) x = t τ k := by
  have h : ∀ x : Letter Dw, expo Dw (Finsupp.single (b, R, .inl (τ, (k : ℕ))) 1) x =
      if (⟨τ, k⟩ : Letter Dw) = x then 1 else 0 := by
    intro x
    unfold expo
    rw [Finsupp.sum_single_index (by simp)]
    simp only [letterOf, dif_pos k.2, Option.some.injEq]
  rw [Finset.prod_eq_single (⟨τ, k⟩ : Letter Dw)]
  · rw [h, if_pos rfl, zpow_one]
  · intro x _ hx
    rw [h, if_neg (Ne.symm hx), zpow_zero]
  · intro hx
    exact absurd (Finset.mem_univ _) hx

theorem lgOf_single_inl (w : Pad.Sym E →₀ ℤ) (b : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (k : Fin (Dw.mult τ))
    (hw : w = Finsupp.single (b, R, .inl (τ, (k : ℕ))) 1)
    (v : HeightOneSpectrum (𝓞 F)) [Fact (resP v).Prime] (ε : Ext v) (y : AlgPt Y.Y) :
    UnitAt (below y.1) ((((Y.gr_spec (below y.1)).choose_spec.choose_spec.choose τ k) *
      (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) ∧
    lgOf Y w v ε y =
      Real.log (ε.w (valAt y.1 ((((Y.gr_spec (below y.1)).choose_spec.choose_spec.choose τ k) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        lnStep Z.t (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
            stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ l) (resP v) (b (resP v)) (.inl (τ, (k : ℕ))) := by
  have hp := prod_expo_single (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose b R τ k
  rw [← hw] at hp
  have ht := GradedLogInvariants.GlobalTheory.CompanionTheory.GradedInv.isEqn_prod Y (below y.1) (expo Dw w)
  rw [hp] at ht
  refine ⟨?_, ?_⟩
  · simpa [div_eq_mul_inv] using (Base.isEqn_eqn (divOf Y (expo Dw w)) (below y.1)).iff_unitAt.1 ht
  · rw [GlobalTheory.CovHt.Link.lgOf_eq_stepSumVia, hp]
    congr 2
    unfold GlobalTheory.CovHt.Link.stepSumVia
    rw [hw, Finsupp.sum_single_index (by simp), Int.cast_one, one_mul]

end Free

end GlobalTheory.CovHt.RootFirst
