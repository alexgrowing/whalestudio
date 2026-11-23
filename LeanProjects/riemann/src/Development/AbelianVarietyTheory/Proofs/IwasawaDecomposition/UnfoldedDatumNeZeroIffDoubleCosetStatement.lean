import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCoset
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → cst.sharp = true → L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → SameDC (Pr := Pr) cst.sharp i P.1 1 hal → (FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) := by
  first | exact @GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' | exact GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' | (intros; apply GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' <;> assumption)
