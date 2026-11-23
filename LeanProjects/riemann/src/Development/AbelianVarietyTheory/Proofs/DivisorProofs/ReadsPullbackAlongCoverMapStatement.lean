import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsPullbackAlongCoverMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reads_pullback_along_cover_map : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (A : Adl C Y) (p : ℕ) (V V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X), Lies V' V π → ∀ c : V.X → V.X.functionFieldˣ, Reads V p A c → Reads V' p A fun x => Units.map (SmallSec.fnMap π hπ).toMonoidHom (c (π x)) := by
  first | exact @GlobalTheory.LatChain.reads_pull | exact GlobalTheory.LatChain.reads_pull | (intros; apply GlobalTheory.LatChain.reads_pull <;> assumption)
