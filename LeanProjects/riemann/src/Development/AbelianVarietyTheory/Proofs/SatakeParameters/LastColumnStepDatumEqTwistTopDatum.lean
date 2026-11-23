import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.TopPin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem xiOver_eq_XiTopG {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl

theorem xiOver_eq_XiTop : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  intro X Pr R Ch sel S mu cst u n h p Y p'
  exact xiOver_eq_XiTopG Ch sel mu cst n h p Y p'

end GlobalTheory.Mem.Col2
