import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOfParts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.HTSpecAllHodge

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.HTSpecB

open GlobalTheory.HTLink

def HTSpecGood : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Formalism.BasicNotions.Loc.FinExt l) (n : ℕ),
    (∀ M : CrystallineSemistableComparison.Model l K.1, M.Sm → (∃ d, SmoothOfRelativeDimension d M.p) → ∃ F : Frame (K := K) M.q n, ∑ a, F.e a = F.d) ∧
    ∃ Φ : ∀ M : CrystallineSemistableComparison.Model l K.1, M.Sm → (∃ d, SmoothOfRelativeDimension d M.p) → ∀ F : Frame (K := K) M.q n, Matrix (Fin F.d) F.Col ℂ_[l],
      (∀ (M : CrystallineSemistableComparison.Model l K.1) (h : M.Sm) (hd : ∃ d, SmoothOfRelativeDimension d M.p) (F : Frame (K := K) M.q n), F.IsHT (Φ M h hd F)) ∧
      ∀ (M M' : CrystallineSemistableComparison.Model l K.1) (h : M.Sm) (h' : M'.Sm) (hd : ∃ d, SmoothOfRelativeDimension d M.p) (hd' : ∃ d, SmoothOfRelativeDimension d M'.p) (F : Frame (K := K) M.q n) (F' : Frame (K := K) M'.q n)
        (u : M'.X ⟶ M.X) (hu : u ≫ M.p = M'.p),
        F.etMat F' (CrystallineSemistableComparison.Model.genMap_q u hu) * Φ M h hd F = Φ M' h' hd' F' * F.hodgeMat F' (CrystallineSemistableComparison.Model.genMap_q u hu)

end CrystallineSemistableComparison.HTSpecB
