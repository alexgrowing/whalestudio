import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivOf
import Formalism.LocalToGlobal.Columns.KernelEquivTrivialTuple

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Red

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m) (Am : Amb X) (u : Pr.Word)

theorem xiEquivC_of {n m2 : ℕ} (hm : R.m = m2 + 2) (hn : 1 ≤ n) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1)
    (hG : GlobTied Ch Gc) (H : IdxHyp Λ Ch sel S Gc n m2)
    (hTh : ThHyp W Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) Am u m2)
    (hXi : ∀ i, i < m2 → ∀ (al : (idxC Λ sel S m2).β i) (be : (idxC Λ sel S m2).β (i + 1)),
      XiLaw Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) (idxC Λ sel S m2) i al be)
    (hPsi : ∀ al : (idxC Λ sel S m2).β m2, PsiLaw Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) (idxC Λ sel S m2) m2 al (alC Λ sel S m2 (m2 + 1) le_rfl))
    (hF : FixE (R := R) Λ m2)
    (hTop : RefKEquiv W Λ Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) (exceptional_primes_trivial_tuple sel S) m2 Am u (m2 + 1)) :
    XiEquiv W Λ Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) Am u
      (refXi1 Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) (idxC Λ sel S m2) (exceptional_primes_trivial_tuple sel S) m2 (alC Λ sel S m2) u) :=
  kernelEquiv_trivialTuple W Λ Ch sel S (cstC Ch sel S Gc n) Am u m2 hX hPr (by omega) hTh (idxC_ok hm hn hX hPr hCh h4 hG H) hXi hPsi hF hTop

end Red

end Formalism.L2.Ker
