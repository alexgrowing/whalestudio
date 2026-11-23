import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfBases
import Formalism.LocalToGlobal.Columns.RowFormsSum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

namespace GlobalTheory.Mem.ColTie

theorem ipK_eq_card_mul_ipLev {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P) :
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  have h0 : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := levelSumX W Ch sel mu P (mtildeOk W Ch sel mu hX P) (mtildeKOk W Ch sel mu hX) z.1 z'.1 z.2 z'.2
  unfold ipLev ipK
  rw [h1, mul_inv_cancel_left₀ h0]

end GlobalTheory.Mem.ColTie
