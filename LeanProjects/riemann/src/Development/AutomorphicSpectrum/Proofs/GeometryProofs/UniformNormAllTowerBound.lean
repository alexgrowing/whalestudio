import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightZeroSectionMembership
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormTowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllTowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsTowerBoundStatement

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem descent_small : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (Fr : Small.GenFrame (o.toTowerOrigin.Or B b)) (Z : Comp Xo c) (Rd : Reading Fr h Z) (_ : GeoRead Rd) (u : GlobalTheory.AllWt.Weight Dw) (R : ℝ), (∀ τ, StrictAnti (u τ)) → 0 ≤ R → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∃ f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0), evC h Z f = trOf Rd u s ∧ (∀ σ, GoodEmb c σ → ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ (o.toTowerOrigin.Or B b).Fl.deg * R) ∧ ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal → ∀ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ((-((vLa la (p : c.F) : ℝ) * (if p ∈ o.toTowerOrigin.S B then exTwo E p else 0) * GlobalTheory.CovHt.l1 u) : ℝ) : EReal) ≤ v f := by
  intro hG E _ _ _ _ H Dw l Xo c r U h e hL hU x hx Y _ T o B b Fr Z Rd hGR u R hu hR s hs
  have hp : 1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
    have h1 := o.toTowerOrigin.j_eq
    have h2 := T.j_pos
    have h3 := T.j_lt
    omega
  obtain ⟨f, hfS, hfZ, hev⟩ := GlobalTheory.T.comp_laws_tower_bound hG E H Dw l Xo c r U h e hL Y T o B b Fr Z Rd hGR u s hs.1
  have harch := GlobalTheory.T.uniform_norm_tower_bound hG E H Dw l Xo c r U h e hL x hx Y T o B b Fr Z Rd hGR u s R hR hs.2 f hfS hev
  refine ⟨f, GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn E H Dw l Xo c r U h e hL hp.1 hp.2 x Z u hu f hfS hfZ
      (fun σ hσ => ⟨_, harch σ hσ⟩), hev, harch, ?_⟩
  exact GlobalTheory.T.uniform_all_tower_bound hG E H Dw l Xo c r U h e hL hU Y T o B b Fr Z Rd hGR u s hs.1 f hfS hfZ hev

end GlobalTheory.CompanionTheory.Ar.Plug
