import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows

theorem exists_htNums_of_kerSide_lastSide :
    ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [DecidableEq Pl] [Fintype Emb] (R : RecNums J Pl) (C CT A : ℝ)
      (P : (J → Emb → ℝ) → Prop), 0 ≤ C → 0 ≤ CT → 2 * (16 + CT) ≤ R.Ch → 6 * C + 1 + 2 * C * C ≤ R.Ch →
      4 * C * (CT + C) ≤ R.Ch → KerSide R Emb C P → LastSide R CT A →
      ∃ hn : HtNums R Emb, hn.hPn = A ∧ P hn.sz := by
  intro J Pl Emb _ _ _ _ R C CT A P hC hCT h1 h2 h3 hK hL
  obtain ⟨g0, MainNotions, logOm, logth0, logh, logh', vv, logg, a1, a2, a3, a4, a5, a6, a7, a8, a9, hP⟩ := hK
  obtain ⟨bT, nτ, lam1, D0, D1, logc, logxi, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hL
  refine ⟨{ hPn := A, g0 := g0, MainNotions := MainNotions, logOmτ := logOm, logth0 := logth0, logh := logh, logh' := logh', vv := vv,
            logg := logg, C2 := C, Cth := C, C4 := C, c5 := C, c6 := C, CT := CT, C8 := C, Ce := C, ev := 0, bT := bT,
            nτ := nτ, lam1 := lam1, D0 := D0, D1 := D1, logc := logc, logxi := logxi, Cev := 0,
            i1 := a1, i2 := a2, i3 := a3, i4 := a4, i5 := a5, i6 := a6, i7 := a7, i8 := a8, i9 := a9,
            i10 := ⟨hC, hC, hC, hC, hC, hC, hC⟩,
            t1 := by simpa using b1, t2 := b2, t3 := b3, t4 := b4, t5 := b5, t6 := b6, t7 := b7, t8 := b8, t9 := b9,
            t10 := ⟨b10, b11, hCT⟩, t11 := ⟨by simp, le_rfl⟩,
            k1 := by linarith, k2 := by linarith, k3 := by linarith }, rfl, hP⟩

end GlobalTheory.ColRows
