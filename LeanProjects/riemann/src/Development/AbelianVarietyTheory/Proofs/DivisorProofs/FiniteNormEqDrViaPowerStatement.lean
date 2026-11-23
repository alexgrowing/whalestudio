import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormEqDrViaPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrViaNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_eq_drVia_power : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 D.what₂.LL)), (p : 𝓞 D.what₂.LL) ∈ v.asIdeal → ∀ (e : Ext v) (y : AlgPt (Φ.C k).Y), finN Φ k la v e y f = drVia Φ k la p y.1 (ioOf p e) f ^ (-Real.log (e.w p) / Real.log p) := by
  first | exact @GlobalTheory.CovHt.Link.finN_eq_drVia_rpow | exact GlobalTheory.CovHt.Link.finN_eq_drVia_rpow | (intros; apply GlobalTheory.CovHt.Link.finN_eq_drVia_rpow <;> assumption)
