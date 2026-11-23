import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def congrH {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (β : HermE D r) : HermE D r :=
  ⟨(a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a, by
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have hβ := β.2
    have hm : ∀ (X Y : Matrix (Fin r) (Fin r) D.host.E),
        (X * Y).map (D.sp.cm.sig : D.host.E → D.host.E) =
          X.map (D.sp.cm.sig : D.host.E → D.host.E) * Y.map (D.sp.cm.sig : D.host.E → D.host.E) :=
      fun X Y => Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [hm, hm, Matrix.transpose_mul, Matrix.transpose_mul, hβ]
    have h2 : ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = a := by
      ext i j; simp [hσ]
    rw [h2, Matrix.mul_assoc]⟩

def IsBlockNF {r : ℕ} (t : ℕ) (β : HermE D r) : Prop :=
  ∃ h : t < r, (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → β.1 i j = 0) ∧
    (β.1.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
