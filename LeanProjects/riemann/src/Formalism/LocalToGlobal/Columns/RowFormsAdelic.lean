import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.AdelicLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def rf_onDeco {X : Fields} {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) : OnDeco n ST SG Λ.grp (formGSD C Λ) where
  eG := MulEquiv.refl _
  eD := Equiv.refl _
  smul := fun _ _ => rfl

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hc : Formalism.BasicNotions.CMData X.F X.E)

instance rf_neZero_X' (R : Ranks) : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩

instance rf_neZero_nV (R : Ranks) : NeZero R.nV := ⟨(nV_pos R).ne'⟩

def mtildeAd (P : LevFam X.E X.K R.r Pr.vGs) : GSD X.K :=
  adGSD hc (rf_onDeco (rowVal W (rowSG Pr sel mu)) (rowTy Ch sel mu P).inv)

def mtAd (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : GSD X.K :=
  adGSD hc (rf_onDeco (mtVal W j (rowSG Pr sel mu)) (mtTy Ch sel mu P j).inv)

open Classical in

def mtildeAdIso (P : LevFam X.E X.K R.r Pr.vGs) (hG : UnimodGenus hc (R.N R.m - 1)) (hR : Formalism.L2.DIV.RedSurj)
    (hT : Formalism.L2.DIV.IsSplitSet (∅ ∪ rowSG Pr sel mu)) :
    GSD.Iso (mtildeAd W Ch sel mu hc P) (mtildeGSD W Ch sel mu P) :=
  adelicIsoG hc _ _ _ _ _ hG hR hT (Finset.disjoint_empty_left _)

open Classical in

def mtAdIso (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) (hG : UnimodGenus hc R.nV) (hR : Formalism.L2.DIV.RedSurj)
    (hT : Formalism.L2.DIV.IsSplitSet (∅ ∪ rowSG Pr sel mu)) :
    GSD.Iso (mtAd W Ch sel mu hc P j) (mtGSD W Ch sel mu P j) :=
  adelicIsoG hc _ _ _ _ _ hG hR hT (Finset.disjoint_empty_left _)

end Rows

end Formalism.L2.Col
