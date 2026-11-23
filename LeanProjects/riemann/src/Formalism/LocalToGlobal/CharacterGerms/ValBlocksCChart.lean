import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.ValBlocksChart

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Gen

variable {d : ℕ} [NeZero d] (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

abbrev rdS (o : Orb) : RowData C V d (fun _ => I0 o) (JJ fun _ => I0 o) := (Y.rawSelf (p o)).rowData (H o)

def imgFamS {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_self (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : ValO (fun o => rdS Y p H o) N (imgFamS Y p Ls n pl) ν := by
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have key := val_self (hs := hs) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po) (hQ := hQ)
    (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hg)
  exact WithBot.coe_le_coe.1 (hν.trans key)

end Gen

section Two

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y 2 (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

theorem valBlocksC_chart (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : ∀ o, Flag (rdS Y p H o)) (nW : ℕ) (hn : nW ≤ 2 * N + 1)
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (hM : BlockMembershipSelfConjugate (fun o => rdS Y p H o) N F (imgFamS Y p Ls n pl) gaC)
    (hA : ∀ o, (rdS Y p H o).Alt) (hj : ∀ o, (rdS Y p H o).j' < (rdS Y p H o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (rdS Y p H o).rkF 0 s) :
    ValBlocksC (fun o => rdS Y p H o) F nW gaC ν :=
  valBlocksC_G (hV := valO_self (hν := hν) (hs := hs) (hv := hv) (pl := pl)) (hJ := jetProd) (F := F) (nW := nW)
    (hn := hn) (gaC := gaC) (hM := hM) (hA := blkAdmC (F := F) (gaC := gaC) (hA := hA) (hj := hj) (hga := hga))

end Two

end Formalism.L2.FormalSeriesBounds.RF
