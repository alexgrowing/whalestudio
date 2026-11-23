import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def corrM (M : Model l K) (T : Corr l M.X) : Model l K := ⟨T.Z, T.p ≫ M.p⟩

def corrP (M : Model l K) (T : Corr l M.X) : E.gb (corrM M T) ⟶ E.gb M :=
  GlobalTheory.Et.geomMap (PadicAlgCl l) (corrM M T).q (Model.genMap (M := corrM M T) (N := M) T.p rfl) (Model.genMap_q (M := corrM M T) (N := M) T.p rfl)

def HkOfPush : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K) (T : Corr l M.X)
  (hr : T.r ≫ M.p = T.p ≫ M.p) (j : ℕ) (t : (corrM M T).V j →ₗ[ℚ_[l]] M.V j), LateralTheory.EtaleTrace.IsPush l (corrP M T) j t →
  IsHk M T hr j (t ∘ₗ Model.pullV (M := corrM M T) (N := M) T.r hr j)

end UpperTheory.Ru.crystallineComparison
