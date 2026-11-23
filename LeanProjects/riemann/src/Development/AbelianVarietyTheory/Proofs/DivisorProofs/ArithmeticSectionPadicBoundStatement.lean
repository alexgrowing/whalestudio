import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSectionPadicBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_section_padic_bound : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw) (g : Rul s.Xo κ.c), g ∈ secZ s.Xo κ.c (exOf S.Dw la 0) → (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (pl : HeightOneSpectrum (𝓞 κ.c.F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 κ.c.F) ∈ pl.asIdeal → ∀ (T : CDVR) (io : κ.c.F →+* T.Fr) (e : ℕ), OverLa pl T.V io e → ∀ y : IntFr s.Xo κ.c T io, T.FinRes → (letI := io.toAlgebra; AllWt.LiesOn Z y.1) → ∀ jm : T.Fr →+* ℂ_[p], (∀ z : T.Fr, z ≠ 0 → ‖jm z‖ = (p : ℝ) ^ (-((vV T.V z : ℝ) / (vV T.V (io (p : κ.c.F)) : ℝ)))) → ∃ x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X, drAt Φ k la p x ((Φ.C k).val g) = ‖jm (evI y g)‖ := by
  first | exact @GlobalTheory.CovHt.Link.exists_pt_drAt_eq | exact GlobalTheory.CovHt.Link.exists_pt_drAt_eq | (intros; apply GlobalTheory.CovHt.Link.exists_pt_drAt_eq <;> assumption)
