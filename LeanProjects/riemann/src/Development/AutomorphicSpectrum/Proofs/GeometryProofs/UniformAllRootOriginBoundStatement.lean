import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformAllRootOriginBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntMemModelSmall
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdZpowLe
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_all_root_origin_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → FinTr.Linked Rd → ∀ B₁ : Finset RM.Ω, ∃ (B₂ : Finset RM.Ω) (B₃ : Finset (Om Z)), ∀ (A : Subring RM.Ω), (↑B₁ : Set RM.Ω) ⊆ A → (↑B₂ : Set RM.Ω) ⊆ A → ∀ (A' : Subring (Om Z)), (↑B₃ : Set (Om Z)) ⊆ A' → ∀ (p : ℕ) [Fact p.Prime] (ev₁ : A →+* PadicAlgCl p), (∀ x, IsAlgebraic ℤ (ev₁ x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (y : IntFr Xo c T io) (ι : T.Fr →+* PadicAlgCl p) (ev : A' →+* T.Fr), (p : 𝓞 c.F) ∈ la.asIdeal → OverLa la T.V io e₀ → y.IsAlg → (∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x) → FinTr.RegAt h Z io A' ev y.1 → (∀ a : A', ∃ ha : Rd.φ a ∈ A, ev₁ ⟨_, ha⟩ = ι (ev a)) → ∃ z ∈ Small.algPts p (mCoordIdeal RM.y), ∃ rec : RootIx Dw → ℝ, (∀ b (hb : b ∈ A), b ∈ B₁ → Small.HasVal RM.y 0 b z (ev₁ ⟨b, hb⟩)) ∧ (∀ r', 0 < rec r' ∧ |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ (if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Real.log p) ∧ ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∀ f ∈ Rec.secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ∀ s : ℝ, nval T.V e₀ (evI y f) = ((ramOverZ la * s : ℝ) : EReal) → ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound | exact GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound <;> assumption)
