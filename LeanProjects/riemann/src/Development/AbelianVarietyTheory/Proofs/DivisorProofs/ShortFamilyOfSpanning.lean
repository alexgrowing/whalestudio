import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

theorem GlobalTheory.HSApp.shortFamily_of_spanning : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, ∀ (Λ : ℝ) (m : ℕ) (v : Fin m → Cusp Z U (P.wt j)), (∀ i, v i ∈ latOn U Z _) → Submodule.span c.F (Set.range v) = ⊤ → (∀ i σ, petOn U x V dict Z (wtOf Dw (P.wt j) 0) σ (v i).1 ≤ Λ) → (h.data f₁ f₂ th k).ShortFamily j Λ := by
  intro E _ _ _ H Dw l Xo c TF Z r U P R ω x D V dict h f₁ f₂ th k j hj Λ m v hv hs hn
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' c.F v
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  let b := Module.Basis.mk hli (by rw [hsp, hs])
  have hcard : Fintype.card κ = latRank c.F ((h.data f₁ f₂ th k).M j) := by
    rw [(h.data f₁ f₂ th k).latRank_M j, ← (h.equivV f₁ f₂ th k hj).finrank_eq, Module.finrank_eq_card_basis b]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => h.equivV f₁ f₂ th k hj (v (a (e i))), fun i => ?_, ?_, fun i σ => ?_⟩
  · exact (h.equivV_mem f₁ f₂ th k hj _).2 (hv _)
  · exact ((hli.comp e e.injective).map' _ (h.equivV f₁ f₂ th k hj).ker)
  · rw [h.nrm_equivV f₁ f₂ th k hj]
    exact hn _ σ
