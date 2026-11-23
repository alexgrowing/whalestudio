import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS
import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.valBlocksS_of_blkMemS :
    ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (hd : ZMod d), hd + hd = 0 →
    ∀ (Orb : Type) [Fintype Orb] (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ),
    ValO X n FFimg ν → ∀ (F : ∀ o, RF.Flag (X o)) (nW : ℕ), nW ≤ 2 * n + 1 → ∀ ga : Orb → ZMod d → ℕ → ℕ,
    PlaneBlockProductsMemFamily hd X n F FFimg ga → (∀ o, (X o).Alt) → (∀ o, (X o).j' < (X o).n) →
    (∀ o s, (X o).rkF 1 (s + hd) = (X o).rkF 0 s) → (∀ o s k, ga o s k ≠ 0 → k ≤ (X o).rkF 0 s) →
    ValBlocksS hd X F nW ga ν := by
  intro C _ _ V d _ hd hhd Orb _ I J _ _ X n FFimg ν hV F nW hnW ga hMem hAlt hj hrk hga
  intro L hAtt hOne hRows hWt
  have hwt : ∀ o, ∀ q ∈ L o, ∀ (g : Fin 2) (a : ZMod d) (k : ℕ),
      GlobalTheory.wt (X o) q.1 g a k ≠ 0 → k ≤ (X o).rkF g a := by
    intro o q hq g a k hne
    fin_cases g
    · have hle : GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k ≤ ga o a k := by
        rw [← hWt o a k]
        exact le_sum_map (L o) (fun q => GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k) hq
      apply hga o a k
      have : GlobalTheory.wt (X o) q.1 0 a k ≠ 0 := hne
      omega
    · have hs : a + hd + hd = a := by rw [add_assoc, hhd, add_zero]
      have hle : GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k ≤ ga o (a + hd) k := by
        rw [← hWt o (a + hd) k]
        exact le_sum_map (L o)
          (fun q => GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k) hq
      rw [hs] at hle
      have hne' : GlobalTheory.wt (X o) q.1 1 a k ≠ 0 := hne
      have h0 : ga o (a + hd) k ≠ 0 := by omega
      have := hga o (a + hd) k h0
      rw [← hrk o (a + hd), hs] at this
      exact this
  have hOK : ∀ o, ∀ q ∈ L o, GlobalTheory.AttainsOK (X o) (F o) q.1 q.2 := fun o q hq =>
    attainsOK_of (X o) (F o) (Or.inl (hAlt o)) (hj o) q.1 q.2 (hwt o q hq) (hAtt o q hq)
  have hsum : ∑ o, (List.map (fun q => GlobalTheory.what₂ (X o).n q.1) (L o)).sum ≤ n := by omega
  exact val_lists hV jetProd F L hOK hsum (hMem L hOne hWt)
