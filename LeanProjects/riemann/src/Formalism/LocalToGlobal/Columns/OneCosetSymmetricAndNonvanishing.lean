import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.LocalToGlobal.Columns.ResidueFieldUnfoldingClaimsHold

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section J

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem oneCosetSymmetric_and_nonvanishing (σ : X.K →+* ℂ) {m2 : ℕ} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} (hB : OcbBase Ch sel mu cst m2)
    (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) (b3 : LiftFromResidueParabolicProduct Ch sel mu cst m2) (hG : OcbGrpGLoc Ch sel mu cst m2)
    (hC : OcbChrGLoc Ch sel mu cst m2) (hΛ : OcbLevIs Ch Λ m2) : OneCosetSym Ch sel mu cst Λ m2 ∧ NonVanSym Ch sel mu cst m2 :=
  oneCosetSym_of σ hB hQ residueFieldUnfolding_claims_hold.1 residueFieldUnfolding_claims_hold.2 (reductionExistsInLatticeStabilizer_holds Ch sel mu cst σ m2) b3 hG hC hΛ

end J

end Formalism.L2.Col
