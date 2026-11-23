import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModel
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenChart
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenGen

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles MonoidalCategory CartesianMonoidalCategory MonObj

namespace PositivityTheory.HtPt.Hcptgen

theorem hcpt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), CharZero Ω ∧ IsLocallyNoetherian 𝔐.X ∧ IsProper (Limits.pullback.snd 𝔐.t.G.hom 𝔐.ξ) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (f : Ω →+* k), Nonempty (TateIso D k (Over.mk (spMap f ≫ 𝔐.ξ) ⟶ 𝔐.t.G) (fun a g => g ≫ 𝔐.t.act.act a) (fun n g g' c => Out.WeilIs 𝔐.t.G 𝔐.t.PP.L n g g' (unitOn c)))) ∧ 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ ∀ s, mseg y s ≠ 0 → IsNoetherianRing (chartRing o (mseg y) s) ∧ IsIntegrallyClosed (chartRing o (mseg y) s) ∧ IsFractionRing (chartRing o (mseg y) s) Ω ∧ ∃ x : Sp (chartRing o (mseg y) s) ⟶ 𝔐.X, spMap (algebraMap (chartRing o (mseg y) s) Ω) ≫ x = 𝔐.ξ ∧ ∀ q : Cpt 𝔐.ξ, q.1 ∈ Set.range x ↔ (InChart 𝔐.ξ (mseg y) s q ∧ OverZp 𝔐 p q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp _ o _ _ ho
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  refine ⟨hchar, ?_, isProper_gen 𝔐, fun k _ _ f => ?_, two_mul_finrank 𝔐, fun s => (finrank_Vgen 𝔐 s).2,
    fun s hs => chart_loc (x := mseg y) 𝔐.all 𝔐.tie 𝔐.normal hp.out ho hs _ (chartRing_mseg y s hs)⟩
  · obtain ⟨s, h1, -, -⟩ := ChartFType.main 𝔐.X Ω 𝔐.ξ _ _ 𝔐.all 𝔐.tie
    exact LocallyOfFiniteType.isLocallyNoetherian s
  · obtain ⟨x, hx⟩ := exists_lift 𝔐
    let g : CommRingCat.of (KA l) ⟶ CommRingCat.of k := Spec.preimage ((spMap f ≫ x) ≫
      Limits.pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
    obtain ⟨-, I, -⟩ := Y.oF.geom k (spMap f ≫ x) g.hom (Spec.map_preimage _).symm
    obtain ⟨I₁, -⟩ := (XR.tateIsoAt_move E H D Y.X (Xo.XF c) Y.t Y.oF.t Y.j Y.m k (spMap f ≫ x) _ rfl).2 I
    obtain ⟨I₂, -⟩ := (XR.tateIsoAt_move E H D Y.X 𝔐.X Y.t 𝔐.t 𝔐.f 𝔐.m k (spMap f ≫ 𝔐.ξ) ((spMap f ≫ x) ≫ Y.j)
      (by rw [Category.assoc, Category.assoc, hx])).1 I₁
    exact ⟨I₂⟩

end PositivityTheory.HtPt.Hcptgen
