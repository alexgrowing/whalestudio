import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeBound
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThirdStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourthStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_system_hodge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (s : Fin (Dc.N - Dc.j) → Or.𝔐.Li) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Submodule.span Ω (Set.range (b ∘ headIdx Dc.j_le_N)) = Hd.F τ → (∀ k, s k ∈ Or.𝔐.Vgen (Or.sm τ)) → (∀ k, Or.i τ (b (tailIdx Dc.j_le_N k)) - s k ∈ Or.𝔐.V (Or.bg τ) ⟨centre z, h⟩) → (Or.𝔐.V (Or.sm τ)).IsFrameAt s ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → G.PosDef → ∃ Γ : Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z s Γ ∧ Γ.PosDef ∧ quotNormSq Dc.j_le_N G = Γ.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det | exact GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det | (intros; apply GlobalTheory.CompanionTheory.Ar.SmallGram.quotNormSq_eq_det <;> assumption)
