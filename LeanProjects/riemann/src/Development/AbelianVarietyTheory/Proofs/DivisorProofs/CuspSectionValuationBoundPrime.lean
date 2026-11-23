import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionIntegralReductionDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceNormBoundIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeBoundAllPointsStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CovHt.Link

theorem le_recVals_of_finN_le : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ (la : AllWt.Weight S.Dw) (g : Rul s.Xo κ.c), g ∈ secZ s.Xo κ.c (exOf S.Dw la 0) → g ∈ suppOn Z → (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (pl : HeightOneSpectrum (𝓞 κ.c.F)) (p : ℕ), p.Prime → (p : 𝓞 κ.c.F) ∈ pl.asIdeal → ∀ a : ℝ, (∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (p : 𝓞 D.what₂.LL) ∈ v.asIdeal → ∀ e y, finN Φ k la v e y ((Φ.C k).val g) ≤ NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL) ^ a) → ∀ w ∈ (recVals s.Xo κ.c).1 pl, (((vLa pl (p : κ.c.F) : ℝ) * a : ℝ) : EReal) ≤ w g := by
  intro h2 hH D A N j S κ s Φ k Z hO la g hg hs hv pl p hp hpl a hb w hw
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hw
  show (((vLa pl (p : κ.c.F) : ℝ) * a : ℝ) : EReal) ≤ nval T.V e (evI y g)
  letI := io.toAlgebra
  by_cases hZ : AllWt.LiesOn Z y.1
  · obtain ⟨x, hx⟩ := GlobalTheory.T.section_integral_reduction_dvr h2 hH D A N j S κ s Φ k Z hO la g hg hv pl p hpl T io e ho y hy hZ
    refine hx a ?_
    refine GlobalTheory.T.derivative_bound_all_points h2 hH D A N j S κ s Φ k la _ hv p _ (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) ?_ x
    exact GlobalTheory.T.finite_place_norm_bound_integral h2 hH D A N j S κ s Φ k la _ hv p a hb
  · have h0 : evI y g = 0 := hs T.Fr y.1 ((liesOff_iff Z y.1).2 hZ)
    rw [h0, nval_zero]
    exact le_top

end GlobalTheory.CovHt.Link
