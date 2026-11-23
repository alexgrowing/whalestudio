import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def XiTop {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (d : DecoSet X.E (R.N R.m) (Pr.vT u) (rowSG Pr sel mu)) (fr : Frs X.E (R.N R.m) (rowSG Pr sel mu))
    (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  phiT X.K p.deco.1 d.1 x *
    ∏ P : rowSG Pr sel mu,
      PhiTop Ch mu cst.sharp m2 P.1 (prXp X.E R ∘ₗ (fr P).symm.toLinearMap ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
        ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ (fr P).symm.toLinearMap ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
          ((frsF sel mu p P).symm (repY Y))

def IsRowFrame (u : Pr.Word) (d : RowPt Pr R sel mu) (fr : Frs X.E (R.N R.m) (rowSG Pr sel mu)) : Prop :=
  ∀ P : rowSG Pr sel mu,
    prXp X.E R ∘ₗ (fr P).symm.toLinearMap = (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∧
    atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ (fr P).symm.toLinearMap =
      ((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)

end GlobalTheory.TwU

end
