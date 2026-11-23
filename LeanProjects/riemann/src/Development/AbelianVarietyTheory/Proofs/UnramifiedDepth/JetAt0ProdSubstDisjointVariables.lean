import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.JetProdSubst

theorem jetAt0_prod_subst : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  intro C _ Orb _ σ _ τ e he P F
  let e' : ∀ o, σ o ↪ τ := fun o => ⟨e o, fun x y h => by
    have h1 : (⟨o, x⟩ : Σ o, σ o) = ⟨o, y⟩ := he h
    simpa using h1⟩
  have hd : ∀ i j x y, e' i x = e' j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (he (a₁ := ⟨i, x⟩) (a₂ := ⟨j, y⟩) h)
  rw [← GlobalTheory.JetProd.jetAt0_prod_rename e' hd]
  congr 1
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

end GlobalTheory.JetProdSubst
