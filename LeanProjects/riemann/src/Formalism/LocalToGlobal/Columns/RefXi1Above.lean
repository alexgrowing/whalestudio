import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.XiRef

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Ref1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)

def refXi1 : XiFam Pr R u := fun i p p' x => XiRef Ch sel mu cst L m2 al i (liftQ hQ p) (liftQ hQ p') x

theorem refXi1_above (hm : R.m = m2 + 2) (i : ℕ) (hi : R.m ≤ i) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs)
    (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    refXi1 Ch sel mu cst L hQ m2 al u i p p' x = 0 := by
  unfold refXi1 XiRef
  rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]

def refArg1 {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hm : R.m = m2 + 2) (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
    (H : XiHyp W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u) G) : ChainArg W Λ G u :=
  ChainArg.ofXi hE { H with above := fun i hi p p' x => refXi1_above Ch sel mu cst L hQ m2 al u hm i hi p p' x }

end Ref1

end Formalism.L2.Col
