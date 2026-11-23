import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelEqParahoricCategory
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_eq_parahoric_category : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h ρ : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1) → (∀ (g : ↥lev.H) (r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h → (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) → ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r) → ∃ lev' : LevI X.E X.K (R.N j) P.1, lev'.H = (prCat (Pr := Pr) cst.sharp j P.1 (ρ * h)).subgroupOf (GLint X.E (R.N j) P.1) ∧ (∀ (g : ↥lev'.H) (r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (ρ * h) → (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) → ((lev'.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P (ρ * h) r) := by
  first | exact @GlobalTheory.Proof.level_eq_parahoric_category.main | exact GlobalTheory.Proof.level_eq_parahoric_category.main | (intros; apply GlobalTheory.Proof.level_eq_parahoric_category.main <;> assumption)
