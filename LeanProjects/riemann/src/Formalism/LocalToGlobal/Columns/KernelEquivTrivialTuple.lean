import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Asm

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {Am : Amb X} {u : Pr.Word}

theorem xiEquiv_one (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hM : MatEquiv W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2))
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h1 : Cp1EquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY)
    (hTop : RefKEquiv W Λ Ch sel mu cst hQ m2 Am u (m2 + 1)) :
    XiEquiv W Λ Ch sel mu cst Am u
      (refXi1 Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) hQ m2 (oneAl Λ sel mu m2) u) := by
  refine xiEquiv_of_refK fun i => ?_
  rcases lt_trichotomy i m2 with h | h | h
  · exact refKEquiv_of_mat h hM
  · subst h
    exact referenceKernelEquiv_of_lastComponent hX hPr hF hY h1
  · rcases Nat.lt_or_ge (m2 + 1) i with h' | h'
    · exact refKEquiv_above h'
    · have e : i = m2 + 1 := by omega
      subst e
      exact hTop

end Asm

section Mu0

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Am : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem kernelEquiv_trivialTuple (hX : X.Ok) (hPr : Pr.Ok) (hm : m2 + 1 < R.m) (hTh : ThHyp W Ch sel (mu0 X.F X.E X.K S) cst Am u m2) {G : ChGlob X R.m}
    (hL : (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).Ok Ch sel (mu0 X.F X.E X.K S) cst G m2)
    (hXi : ∀ i, i < m2 → ∀ (al : (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).β i)
      (be : (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).β (i + 1)),
      XiLaw Ch sel (mu0 X.F X.E X.K S) cst (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2) i al be)
    (hPsi : ∀ al, PsiLaw Ch sel (mu0 X.F X.E X.K S) cst (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2) m2 al
      (oneAl Λ sel (mu0 X.F X.E X.K S) m2 (m2 + 1) le_rfl))
    (hF : FixE (R := R) Λ m2) (hTop : RefKEquiv W Λ Ch sel (mu0 X.F X.E X.K S) cst (exceptional_primes_trivial_tuple sel S) m2 Am u (m2 + 1)) :
    XiEquiv W Λ Ch sel (mu0 X.F X.E X.K S) cst Am u
      (refXi1 Ch sel (mu0 X.F X.E X.K S) cst (oneIdx Λ (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2) (exceptional_primes_trivial_tuple sel S) m2
        (oneAl Λ sel (mu0 X.F X.E X.K S) m2) u) :=
  xiEquiv_one hX hPr hF (matrix_equivariance_trivial_tuple W Ch sel S cst _ Am u m2 hm hPr hTh hL hXi) (coupling_index_set_finite sel _ cst _ u m2 _)
    (penultimate_equivariance_trivial_tuple W Ch sel S cst _ Am u m2 hm hPr hTh hL _ _ hPsi) hTop

end Mu0

end Formalism.L2.Col
