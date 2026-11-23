import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
theorem _root_.GlobalTheory.T.phi_invariance_ramified_place_sharp : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (sharp : Bool) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → (qOf P.1).Prime → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 → P.1 ∈ Pr.vGs → sharp = true → ∀ κ ∈ Jat (Pr := Pr) (R := R) sharp (i + 1) P.1, ∀ x, PhiAt Ch mu sharp i P.1 (κ.toLinearMap ∘ₗ x) * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) = lamRow Ch mu sharp (i + 1) P.1 κ.toLinearMap * PhiAt Ch mu sharp i P.1 x :=
  fun Ch sel _ mu cst sharp _ P hi _ _ _ _ _ hκ x => GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst sharp hi P hκ x
