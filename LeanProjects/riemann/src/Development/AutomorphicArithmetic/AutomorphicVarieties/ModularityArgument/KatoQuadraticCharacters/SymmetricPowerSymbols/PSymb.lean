import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SiegelAdmissibleToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.pSymb :
    UpperTheory.V.Z.Kato.Sym.PSymb := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t ht
  unfold UpperTheory.V.Z.Kato.Sym.Lv at hL
  unfold UpperTheory.V.Z.Kato.Sym.IsSec at ht
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := UpperTheory.V.Z.Kato.Sym.rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := UpperTheory.V.Z.Kato.Sym.admB Ω ε X
  have key : ∀ (s : Gal(Ω/ℚ)) (x y : UpperTheory.V.Z.Kato.Sym.Row M), UpperTheory.V.Z.Kato.Sym.Ok x y →
      ∃ f ∈ X.Un m, UpperTheory.V.Z.Kato.Sym.Mv X m (X.gal s) s
        (t (UpperTheory.V.Z.Kato.Sym.sg X c M (UpperTheory.V.Z.Kato.Sym.gr M s⁻¹ x)) (UpperTheory.V.Z.Kato.Sym.sg X d M (UpperTheory.V.Z.Kato.Sym.gr M s⁻¹ y)))
        (t (UpperTheory.V.Z.Kato.Sym.sg X c M x) (UpperTheory.V.Z.Kato.Sym.sg X d M y)) f := by
    intro s x y hxy
    obtain ⟨hx0, hy0, -⟩ := hok _ _ ((hok x y hxy).2.2.1 s⁻¹)
    have hsx := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X c M hc hc6 hM hcM _ hx0
    have hsy := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X d M hd hd6 hM hdM _ hy0
    have hP := (ht _ _ hsx.1 hsy.1).1
    have hx1 := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X c M hc hc6 hM hcM x (hok x y hxy).1
    have hy1 := UpperTheory.V.Z.Kato.Sym.sgB Ω ε X d M hd hd6 hM hdM y (hok x y hxy).2.1
    have ex := UpperTheory.V.Z.Kato.Sym.mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ hP
    have ex1 := ex.1 (t (UpperTheory.V.Z.Kato.Sym.sg X c M x) (UpperTheory.V.Z.Kato.Sym.sg X d M y))
    rw [hsx.2.2.1, hsy.2.2.1, ← (hgr s s⁻¹ x).1, ← (hgr s s⁻¹ y).1, mul_inv_cancel, (hgr 1 1 x).2, (hgr 1 1 y).2] at ex1
    exact ex1 (ht _ _ hx1.1 hy1.1).1
  classical
  refine ⟨fun s x y => if h : UpperTheory.V.Z.Kato.Sym.Ok x y then Classical.choose (key s x y h) else 1, ?_⟩
  unfold UpperTheory.V.Z.Kato.Sym.IsSymb
  intro s x y hxy
  simp only [dif_pos hxy]
  exact Classical.choose_spec (key s x y hxy)
