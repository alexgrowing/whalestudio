import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreePpData
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_degree_pp_data : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : KeyIn L) (th : D.t.PP.L.Sec) (s : Out.H0 D.t.PP.L 1) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)) (e : Fin D.g → D.B.carrier), KeyDeg.SameSec s th → KeyOver (algebraMap (𝓞 L) L) D.t th x v → IsLieBasis v → (∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left) → ∀ (σ : L →+* ℂ) (a : D.Frame σ) (θ : (Fin D.g → ℂ) → ℂ) (W : Matrix (Fin D.g) (Fin D.g) ℂ) (Fd : Set (Fin D.g → ℂ)), a.IsFn s θ → (∀ i, D.IsVec a (e i) (W i)) → IsAddFundamentalDomain a.u.Λ Fd volume → ‖σ (κ L x : L)‖ * ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4 * ((volume Fd).toReal / (Real.pi ^ D.g * ‖W.det‖ ^ 2)) ^ 2 = (2 * Real.pi) ^ (2 * D.g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch.norm_key_of_frame | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch.norm_key_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDegArch.norm_key_of_frame <;> assumption)
