import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate
import Formalism.LocalToGlobal.CharacterGerms.RowTieVal

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)

abbrev rd (o : Orb) : RowData C V d (I o) (JJ (I o)) := (Y.raw (p o)).rowData (H o)

def imgFam : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n) :
    ValO (fun o => rd Y p H o) n (imgFam Y p Ls n) ν := by
  intro Po hPo kind hk S t ht gr hg
  obtain ⟨P, hP, hQ⟩ := hPo
  obtain ⟨f, hf, he⟩ := hv hs P hP Po hQ kind hk S t ht gr hg
  have hx := hν _ ⟨P, hP, f, hf, rfl⟩
  rw [he, map_prod_add] at hx
  exact hx

theorem lower_of_nuPlE (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x := by
  intro x hx
  have h1 : (ν : EReal) ≤ (WithBot.some x : WithBot (WithTop ℝ)) := hν.trans (biInf_le _ hx)
  exact WithBot.coe_le_coe.1 h1

variable (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

def BlockMembershipChart : Prop := BlockMembership (fun o => rd Y p H o) n F (imgFam Y p Ls n) Z ga

def BlockAdmissibleChart : Prop := BlockAdmissible (fun o => rd Y p H o) F Z ga

theorem valBlocks_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_G (valO_of Y p H Ls n ν hν hs hv) hJ F Z ga hM hA

theorem valBlocks_of_nuPlE (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_of Y p H Ls n F Z ga ν (lower_of_nuPlE Y Ls n ν hν) hs hv hJ hM hA

end Formalism.L2.FormalSeriesBounds.RF
