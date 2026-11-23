import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section G

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (I o) (J o)} {n : ℕ}

theorem valBlocks_fin {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (hM : BlockMembership X n F FFimg Z ga)
    (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : ValBlocks X F Z n ga ν :=
  valBlocks_G hV jetProd F Z ga hM (blkAdm X F Z ga hdich hj hga)

end G

section Cc

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ}

theorem valBlocksC_fin {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (nW : ℕ) (hn : nW ≤ 2 * n + 1) (gaC : Orb → ZMod 2 → ℕ → ℕ) (hM : BlockMembershipSelfConjugate X n F FFimg gaC)
    (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n) (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) :
    ValBlocksC X F nW gaC ν :=
  valBlocksC_G hV jetProd F nW hn gaC hM (blkAdmC X F gaC hA hj hga)

end Cc

section FB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
  (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

theorem valBlocks_chart (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n)
    (hM : BlockMembershipChart Y p H Ls n F Z ga)
    (hdich : ∀ o ∈ Z, (rd Y p H o).Alt ∨ ∀ a, (rd Y p H o).big 0 a) (hj : ∀ o ∈ Z, (rd Y p H o).j' < (rd Y p H o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (rd Y p H o).rkF g a) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_fin (valO_of Y p H Ls n ν (lower_of_nuPlE Y Ls n ν hν) hs hv) F Z ga hM hdich hj hga

end FB

end Formalism.L2.FormalSeriesBounds.RF
