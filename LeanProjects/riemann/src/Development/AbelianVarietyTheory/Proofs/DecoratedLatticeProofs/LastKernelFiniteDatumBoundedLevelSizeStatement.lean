import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelFiniteDatumBoundedLevelSize
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  first | exact @GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp | exact GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp | (intros; apply GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp <;> assumption)
