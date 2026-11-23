import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainLevelFamilyExtension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTrueColsRowInt

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
open scoped ComplexOrder Matrix

namespace GlobalTheory.Mem.ColTie

section Mat

end Mat

section Gen

def StarCx {X : Fields} (σ : X.K →+* ℂ) : Prop := ∀ x, σ (star x) = starRingEnd ℂ (σ x)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

abbrev HPm : Matrix (Fin (dimP W Ch sel mu P hX)) (Fin (dimP W Ch sel mu P hX)) X.K :=
  (csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr

abbrev EPm : Matrix (Fin (csdK W Ch sel mu hX).dim) (Fin (dimP W Ch sel mu P hX)) X.K :=
  (csdK W Ch sel mu hX).lvlE (actK W Ch sel mu hX) P.grp P.chr

abbrev NabP : Submodule (𝓞 X.K) (Fin (dimP W Ch sel mu P hX) → X.K) :=
  (csdK W Ch sel mu hX).lvlNab (actK W Ch sel mu hX) P.grp P.chr

abbrev eP (i : Fin (dimP W Ch sel mu P hX)) : Fin (dimP W Ch sel mu P hX) → X.K := Pi.single i 1

theorem ipK_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform (HPm W Ch sel mu P hX) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level W Ch sel mu P hX, ipK_zOf]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px) (t : TupU I U)

end Fam

section TC

attribute [local instance] starE

theorem sig_starCx (B : Base) : StarCx (X := B.fields) (sig B) := fun x => B.starLL_cx x

variable {B : Base} {px : PreX B.toPre} (I : TC B px)

abbrev jT (u : B.Word) (a : I.ι) (hd : Disjoint (B.primes px).vGs (I.Q a)) (hX : B.fields.Ok) :=
  jPer B.wts I.Ch I.sel (I.tup a) I.Ps hX (I.perIn u a).b0 (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz
    (I.perIn u a).H hd (sig B)

end TC

end GlobalTheory.Mem.ColTie
