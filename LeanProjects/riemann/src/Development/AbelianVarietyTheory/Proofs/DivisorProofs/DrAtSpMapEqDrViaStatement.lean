import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtSpMapEqDrVia
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrViaNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.drAt_spMap_eq_drVia : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (φ : K →+* ℂ_[p]) (y : Sp K ⟶ (Φ.C k).Y.X) (f : (Φ.C k).Y.Fn), drAt Φ k la p (spMap φ ≫ y) f = drVia Φ k la p y φ f := by
  first | exact @GlobalTheory.CovHt.Link.drAt_spMap_comp | exact GlobalTheory.CovHt.Link.drAt_spMap_comp | (intros; apply GlobalTheory.CovHt.Link.drAt_spMap_comp <;> assumption)
