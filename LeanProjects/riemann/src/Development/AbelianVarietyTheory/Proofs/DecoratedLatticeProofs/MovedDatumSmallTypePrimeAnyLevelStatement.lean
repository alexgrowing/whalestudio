import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumSmallTypePrimeAnyLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedDatum_small_typePrime_any_level : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 1 < N.R.m → ∀ (P : rowSG Pr sel mu) (h : AutY X N.R i) (h' : AutY X N.R (i + 1)), h ∈ stabL X.E _ (lamYat (Pr := Pr) i P.1) → h' ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1) → LocSmall (Formalism.L2.Col.qOf P.1) (lamYat (Pr := Pr) (R := N.R) i P.1) (lamYat (Pr := Pr) (R := N.R) (i + 1) P.1) (omPhi Ch sel mu cst i P h h') 1 := by
  first | exact @GlobalTheory.Core.Ht2.MovedDatumS.omPhi_locSmall_sharp | exact GlobalTheory.Core.Ht2.MovedDatumS.omPhi_locSmall_sharp | (intros; apply GlobalTheory.Core.Ht2.MovedDatumS.omPhi_locSmall_sharp <;> assumption)
