import Formalism.LocalToGlobal.Columns.ChainLawExt
import Formalism.LocalToGlobal.Columns.ChainLawPhi

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section XiE1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def FirstUnfoldingJInvarianceLaw (i : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (κ : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (κ' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))),
    κ ∈ GLint X.E (R.N i) P.1 → κ' ∈ GLint X.E (R.N (i + 1)) P.1 →
    clL_ext (cOf R i) κ ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N i) (cOf R i) →
    clL_ext (cOf R (i + 1)) κ' ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N (i + 1)) (cOf R (i + 1)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      E1at Ch sel mu cst i P 1 1 (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) =
        LocE.lamGBS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.r R.t (i + 1) (R.N (i + 1)) (cOf R (i + 1))
            (clL_ext (cOf R (i + 1)) κ'.symm).toLinearMap *
          (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ'.symm : X.Eˣ) : X.E))⁻¹ *
          (LocE.lamGBS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.r R.t i (R.N i) (cOf R i) (clL_ext (cOf R i) κ).toLinearMap *
            (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ : X.Eˣ) : X.E))⁻¹) *
          E1at Ch sel mu cst i P 1 1 y

def XiTgtLaw (i : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ κ' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1)), κ' ∈ GLint X.E (R.N (i + 1)) P.1 →
    clL_ext (cOf R (i + 1)) κ' ∈ LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N (i + 1)) (cOf R (i + 1)) →
    ∀ w : HomE X.E (R.N i) (R.N (i + 1)),
      Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B)
          (((qOf P.1 : X.K) ^ cst.B)⁻¹) (PhiAt Ch mu cst.sharp i P.1) (κ'.symm.toLinearMap ∘ₗ w) =
        Loc.E1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1)) (cst.psi P) (LocE.valsQ X.E (qOf P.1) cst.A cst.B)
          (((qOf P.1 : X.K) ^ cst.B)⁻¹)
          (fun x => PhiAt Ch mu cst.sharp i P.1 ((clL_ext (cOf R (i + 1)) κ'.symm).toLinearMap ∘ₗ x)) w

end XiE1

end Formalism.L2.Col
