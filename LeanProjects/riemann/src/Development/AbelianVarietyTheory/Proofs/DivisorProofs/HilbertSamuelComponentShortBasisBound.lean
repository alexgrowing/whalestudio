import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegEqDel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBirationalImageEqTupleHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelBoundOfQuotedTheoremsStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.HSShort

theorem hsClaimS_component_geo : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), ∀ Λ₀ : ℝ, GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ → HSClaimS 26 P.T (CompHt.dimFlag Dw) f₁.n 1 k.abelian₂ k.beta k.LamD k.LamT (Real.log Λ₀) (CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0)) (CompHt.compHeight U x V dict Z (AllWt.wtOf Dw P.u₁ 0)) (Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0))) (AllWt.degOn U x V dict Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k Λ₀ hH
  have hp := CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hb : (h.data f₁ f₂ th k).Birational := hH.bir
  have hd := ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ (h.data f₁ f₂ th k).geom hb hp.2
  have hh := GlobalTheory.T.height_birationalImage_eq_tuple_height hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _ hH.totallyComplex (h.data f₁ f₂ th k).geom hb hp.2
  have hc := GlobalTheory.T.arithmeticHilbertSamuelBound hQ c.F (h.data f₁ f₂ th k) Λ₀ hH _ hh
  have hm := GlobalTheory.T.degree_supLattice_component_eq E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k P.T le_rfl
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  obtain ⟨-, eT, -, en, eL, eb, eD, eT', -⟩ := h.data_numbers f₁ f₂ th k
  rw [← hd, h.d_eq f₁ f₂ th k, eT, en, eL, eb, eD, eT', hm, hD, Int.cast_natCast] at hc
  exact hc

end GlobalTheory.HSShort
